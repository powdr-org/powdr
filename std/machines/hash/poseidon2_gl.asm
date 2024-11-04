use std::array;
use std::check::assert;
use std::utils::unchanged_until;
use std::utils::force_bool;
use std::utils::sum;
use std::convert::expr;
use std::machines::large_field::memory::Memory;
use std::machines::split::split_gl::SplitGL;

// Implements the Poseidon2 permutation for Goldilocks field.
//
// It can be used as general hash fuction by using a sponge construction or,
// by discarding a part of the output, it can be used as compression function
// for building a Merkle tree.
//
// Differently from our Poseidon Goldilocks implementation, we will use a
// state size of 8 field elements instead of 12, matching Plonky3's implementation.
machine Poseidon2GL(mem: Memory, split_GL: SplitGL) with
    latch: latch,
    operation_id: operation_id,
    // Allow this machine to be connected via a permutation
    call_selectors: sel,
{
    // Is this a used row?
    let is_used = array::sum(sel);
    force_bool(is_used);

    // The input data is passed via a memory pointer: the machine will read STATE_SIZE
    // field elements from memory.
    //
    // Similarly, the output data is written to memory at the provided pointer.
    //
    // Reads happen at the provided time step; writes happen at the next time step.
    operation poseidon2_permutation<0>
        input_addr[0],
        output_addr[0],
        time_step ->;

    let latch = 1;
    let operation_id;

    let time_step;

    // Poseidon2 parameters, compatible with our powdr-plonky3 implementation.
    //
    // The the number of rounds to get 128-bit security was taken from here:
    // https://github.com/Plonky3/Plonky3/blob/2df15fd05e2181b31b39525361aef0213fc76144/poseidon2/src/round_numbers.rs#L55

    // Number of field elements in the state
    let STATE_SIZE: int = 8;

    // Half the number of external rounds (half of external rounds happen before and half after the internal rounds).
    let HALF_EXTERNAL_ROUNDS: int = 4;

    // Number of internal rounds
    let INTERNAL_ROUNDS: int = 22;

    // External round MDS matrix
    let MDS = [
        [4, 6, 2, 2, 2, 3, 1, 1],
        [2, 4, 6, 2, 1, 2, 3, 1],
        [2, 2, 4, 6, 1, 1, 2, 3],
        [6, 2, 2, 4, 3, 1, 1, 2],
        [2, 3, 1, 1, 4, 6, 2, 2],
        [1, 2, 3, 1, 2, 4, 6, 2],
        [1, 1, 2, 3, 2, 2, 4, 6],
        [3, 1, 1, 2, 6, 2, 2, 4],
    ];

    // Diagonal of the internal round diffusion matrix
    let DIFF_DIAGONAL = [12216033376705242021, 2072934925475504800, 16432743296706583078, 1287600597097751715, 10482065724875379356, 3057917794534811537, 4460508886913832365, 4574242228824269566];

    let DIFF_MULTIPLIER = 1;

    // External round constants, one STATE_SIZE array for each round
    let EXTERNAL_ROUND_CONSTANTS = [
        [12578764544318200737, 17529487244874322312, 7886285670807131020, 11572758976476374866, 5323617429756461744, 2766252901828231838, 5682345367224914708, 14828835203913492612],
        [14227028876630821888, 4401121311800897944, 9350043436605376040, 16635332319643196323, 17653354571726536749, 10938523927967171405, 13443959161786668970, 3304483495961147300],
        [10614130117109688397, 3168455021757892323, 8191319777620403455, 1409165301955871501, 2851098036599004855, 5910904342370227653, 12906965256452577593, 1446325983400578370],
        [709353063579077124, 4829755133369728407, 15491131302928388465, 14008986064507162301, 12396337209942585769, 12582931927345169831, 12437814383306842903, 1841754590950016055],
        [3737970769775807255, 4043632453527161836, 14119089074600487752, 12841494857048962050, 7827611443821146160, 1210377924565601529, 16261214877113852211, 12103329371965197203],
        [14238676389184304018, 15176458182096690865, 780357387251526735, 15349465161478006477, 17286451399960384764, 13079134536770605075, 8356410918827354631, 15955292684331040254],
        [10768994993414235838, 17790760810741022106, 4258058340480579026, 11495260958956685938, 6757499677441634868, 8154916564929059096, 2491620347296466053, 2539630113571147954],
        [12496384437728543601, 14624197358522713851, 13091146861108865698, 8408456943069069277, 429031222017980611, 11395676813394475848, 16066918610446053799, 6410343575632282534],
    ];

    // Internal round constants, one for each round
    let INTERNAL_ROUND_CONSTANTS = [
        1473335034287276021,
        11944545153990782003,
        13940168329529015387,
        8372698434105336528,
        15678928713513790275,
        6984930233113222930,
        14331318031617034210,
        17505767401781684616,
        17698337720020297936,
        9633568280404517874,
        11117879087462060958,
        4255041930486373420,
        1134773948522875929,
        11154602431214364740,
        10727322033320176806,
        14681358658821901434,
        11951109496186819297,
        5291109736568350150,
        7939321512312132141,
        2652718896006920980,
        1755505308795057920,
        17087002564333290124,
    ];

    // Calculate the addresses and load all the inputs into the first time step
    let input_addr: col[STATE_SIZE];
    address_inc(input_addr_high, input_addr_low);

    let input_low: col[STATE_SIZE];
    let input_high: col[STATE_SIZE];
    // TODO: when link is available inside functions, we can turn this into array operations.
    link if is_used ~> (input_high[0], input_low[0]) = mem.mload(input_addr_high[0], input_addr_low[0], time_step);
    link if is_used ~> (input_high[1], input_low[1]) = mem.mload(input_addr_high[1], input_addr_low[1], time_step);
    link if is_used ~> (input_high[2], input_low[2]) = mem.mload(input_addr_high[2], input_addr_low[2], time_step);
    link if is_used ~> (input_high[3], input_low[3]) = mem.mload(input_addr_high[3], input_addr_low[3], time_step);
    link if is_used ~> (input_high[4], input_low[4]) = mem.mload(input_addr_high[4], input_addr_low[4], time_step);
    link if is_used ~> (input_high[5], input_low[5]) = mem.mload(input_addr_high[5], input_addr_low[5], time_step);
    link if is_used ~> (input_high[6], input_low[6]) = mem.mload(input_addr_high[6], input_addr_low[6], time_step);
    link if is_used ~> (input_high[7], input_low[7]) = mem.mload(input_addr_high[7], input_addr_low[7], time_step);
    link if is_used ~> (input_high[8], input_low[8]) = mem.mload(input_addr_high[8], input_addr_low[8], time_step);
    link if is_used ~> (input_high[9], input_low[9]) = mem.mload(input_addr_high[9], input_addr_low[9], time_step);
    link if is_used ~> (input_high[10], input_low[10]) = mem.mload(input_addr_high[10], input_addr_low[10], time_step);
    link if is_used ~> (input_high[11], input_low[11]) = mem.mload(input_addr_high[11], input_addr_low[11], time_step);
    link if is_used ~> (input_high[12], input_low[12]) = mem.mload(input_addr_high[12], input_addr_low[12], time_step);
    link if is_used ~> (input_high[13], input_low[13]) = mem.mload(input_addr_high[13], input_addr_low[13], time_step);
    link if is_used ~> (input_high[14], input_low[14]) = mem.mload(input_addr_high[14], input_addr_low[14], time_step);
    link if is_used ~> (input_high[15], input_low[15]) = mem.mload(input_addr_high[15], input_addr_low[15], time_step);

    // Assemble the two limbs of the input
    let input = array::zip(input_low, input_high, |low, high| low + 0x10000 * high);

    // Split the output into high and low limbs
    let output_low: col[OUTPUT_SIZE];
    let output_high: col[OUTPUT_SIZE];
    // TODO: turn this into array operations
    link if is_used ~> (output_low[0], output_high[0]) = split_BB.split(output[0]);
    link if is_used ~> (output_low[1], output_high[1]) = split_BB.split(output[1]);
    link if is_used ~> (output_low[2], output_high[2]) = split_BB.split(output[2]);
    link if is_used ~> (output_low[3], output_high[3]) = split_BB.split(output[3]);
    link if is_used ~> (output_low[4], output_high[4]) = split_BB.split(output[4]);
    link if is_used ~> (output_low[5], output_high[5]) = split_BB.split(output[5]);
    link if is_used ~> (output_low[6], output_high[6]) = split_BB.split(output[6]);
    link if is_used ~> (output_low[7], output_high[7]) = split_BB.split(output[7]);

    // Write the output to memory at the next time step
    let output_addr_high: col[OUTPUT_SIZE];
    let output_addr_low: col[OUTPUT_SIZE];
    address_inc(output_addr_high, output_addr_low);
    // TODO: turn this into array operations
    link if is_used ~> mem.mstore(output_addr_high[0], output_addr_low[0], time_step + 1, output_high[0], output_low[0]);
    link if is_used ~> mem.mstore(output_addr_high[1], output_addr_low[1], time_step + 1, output_high[1], output_low[1]);
    link if is_used ~> mem.mstore(output_addr_high[2], output_addr_low[2], time_step + 1, output_high[2], output_low[2]);
    link if is_used ~> mem.mstore(output_addr_high[3], output_addr_low[3], time_step + 1, output_high[3], output_low[3]);
    link if is_used ~> mem.mstore(output_addr_high[4], output_addr_low[4], time_step + 1, output_high[4], output_low[4]);
    link if is_used ~> mem.mstore(output_addr_high[5], output_addr_low[5], time_step + 1, output_high[5], output_low[5]);
    link if is_used ~> mem.mstore(output_addr_high[6], output_addr_low[6], time_step + 1, output_high[6], output_low[6]);
    link if is_used ~> mem.mstore(output_addr_high[7], output_addr_low[7], time_step + 1, output_high[7], output_low[7]);
}
