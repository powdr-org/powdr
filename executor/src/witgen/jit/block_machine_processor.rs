#![allow(unused)]
use std::{
    collections::{BTreeSet, HashSet},
    fmt::Display,
};

use bit_vec::BitVec;
use powdr_ast::analyzed::{AlgebraicReference, Identity};
use powdr_number::FieldElement;

use crate::witgen::{
    evaluators::fixed_evaluator, jit::affine_symbolic_expression::AffineSymbolicExpression,
    machines::MachineParts, FixedData,
};

use super::{
    affine_symbolic_expression::Effect,
    variable::{Cell, Variable},
    witgen_inference::{FixedEvaluator, WitgenInference},
};

/// A processor for generating JIT code for a block machine.
struct BlockMachineProcessor<'a, T: FieldElement> {
    fixed_data: &'a FixedData<'a, T>,
    machine_parts: MachineParts<'a, T>,
    block_size: usize,
    latch_row: usize,
}

impl<'a, T: FieldElement> BlockMachineProcessor<'a, T> {
    /// Generates the JIT code for a given combination of connection and known arguments.
    /// Fails if it cannot solve for the outputs, or if any sub-machine calls cannot be completed.
    pub fn generate_code(
        &self,
        identity_id: u64,
        known_args: BitVec,
    ) -> Result<Vec<Effect<T, Variable>>, String> {
        let connection = self.machine_parts.connections[&identity_id];
        assert_eq!(connection.right.expressions.len(), known_args.len());

        // Set up WitgenInference with known arguments.
        let known_variables = known_args
            .iter()
            .enumerate()
            .filter_map(|(i, is_input)| is_input.then_some(Variable::Param(i)))
            .collect::<HashSet<_>>();
        let fixed_evaluator = FixedEvaluatorForFixedData(self.fixed_data);
        let mut witgen = WitgenInference::new(self.fixed_data, fixed_evaluator, known_variables);

        // In the latch row, set the RHS selector to 1.
        assert!(
            witgen
                .set(
                    &connection.right.selector,
                    self.latch_row as i32,
                    T::one().into()
                )
                .complete
        );

        // For each known argument, transfer the value to the expression in the connection's RHS.
        for (index, expr) in connection.right.expressions.iter().enumerate() {
            if known_args[index] {
                let lhs = Variable::Param(index);
                assert!(
                    witgen
                        .set(
                            expr,
                            self.latch_row as i32,
                            AffineSymbolicExpression::from_known_symbol(lhs, None)
                        )
                        .complete
                );
            }
        }

        // Solve for the block witness.
        // Fails if any machine call cannot be completed.
        self.solve_block(&mut witgen)?;

        // For each unknown argument, get the value from the expression in the connection's RHS.
        for (index, expr) in connection.right.expressions.iter().enumerate() {
            if !known_args[index] {
                let lhs = Variable::Param(index);
                if !witgen
                    .set(
                        expr,
                        self.latch_row as i32,
                        AffineSymbolicExpression::from_unknown_variable(lhs, None),
                    )
                    .complete
                {
                    return Err(format!("Could not solve for args[{index}]"));
                };
            }
        }

        Ok(witgen.code())
    }

    /// Repeatedly processes all identities on all rows, until no progress is made.
    /// Returns the set of incomplete (row, Identity) pairs.
    fn solve_block(
        &self,
        witgen: &mut WitgenInference<T, FixedEvaluatorForFixedData<T>>,
    ) -> Result<(), String> {
        let mut complete = HashSet::new();
        for i in 0.. {
            let mut progress = false;

            for row in (0..self.block_size) {
                for id in self.machine_parts.identities.iter() {
                    if !complete.contains(&(id.id(), row)) {
                        let result = witgen.process_identity(id, row as i32);
                        if result.complete {
                            complete.insert((id.id(), row));
                        }
                        progress |= result.progress;
                    }
                }
            }
            if !progress {
                log::debug!("Finishing after {} iterations", i);
                break;
            }
        }

        let has_incomplete_machine_calls = (0..self.block_size)
            .flat_map(|row| {
                self.machine_parts
                    .identities
                    .iter()
                    .map(move |id| (id, row))
            })
            .filter(|(identity, row)| !complete.contains(&(identity.id(), *row)))
            .any(|(identity, _row)| {
                matches!(
                    identity,
                    Identity::Lookup(_)
                        | Identity::Permutation(_)
                        | Identity::PhantomLookup(_)
                        | Identity::PhantomPermutation(_)
                )
            });

        match has_incomplete_machine_calls {
            true => Err("Incomplete machine calls".to_string()),
            false => Ok(()),
        }
    }
}

pub struct FixedEvaluatorForFixedData<'a, T: FieldElement>(pub &'a FixedData<'a, T>);
impl<'a, T: FieldElement> FixedEvaluator<T> for FixedEvaluatorForFixedData<'a, T> {
    fn evaluate(&self, var: &AlgebraicReference, row_offset: i32) -> Option<T> {
        assert!(var.is_fixed());
        let values = self.0.fixed_cols[&var.poly_id].values_max_size();
        let row = (row_offset + var.next as i32 + values.len() as i32) as usize % values.len();
        Some(values[row])
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use bit_vec::BitVec;
    use powdr_ast::analyzed::{
        AlgebraicExpression, AlgebraicReference, Analyzed, SelectedExpressions,
    };
    use powdr_number::GoldilocksField;

    use crate::{
        constant_evaluator,
        witgen::{
            global_constraints,
            jit::{affine_symbolic_expression::Effect, test_util::format_code},
            machines::{Connection, ConnectionKind, MachineParts},
            FixedData,
        },
    };

    use super::{BlockMachineProcessor, Variable};

    fn generate_for_block_machine(
        input_pil: &str,
        block_size: usize,
        latch_row: usize,
        selector_name: &str,
        input_names: &[&str],
        output_names: &[&str],
    ) -> Result<Vec<Effect<GoldilocksField, Variable>>, String> {
        let analyzed: Analyzed<GoldilocksField> =
            powdr_pil_analyzer::analyze_string(input_pil).unwrap();
        let fixed_col_vals = constant_evaluator::generate(&analyzed);
        let fixed_data = FixedData::new(&analyzed, &fixed_col_vals, &[], Default::default(), 0);
        let (fixed_data, retained_identities) =
            global_constraints::set_global_constraints(fixed_data, &analyzed.identities);

        let witnesses_by_name = analyzed
            .committed_polys_in_source_order()
            .flat_map(|(symbol, _)| symbol.array_elements())
            .collect::<BTreeMap<_, _>>();
        let to_expr = |name: &str| {
            let next = name.ends_with("'");
            let column_name = if next { &name[..name.len() - 1] } else { name };
            AlgebraicExpression::Reference(AlgebraicReference {
                name: name.to_string(),
                poly_id: witnesses_by_name[column_name],
                next,
            })
        };
        let rhs = input_names
            .iter()
            .chain(output_names)
            .map(|name| to_expr(name))
            .collect::<Vec<_>>();
        let right = SelectedExpressions {
            selector: to_expr(selector_name),
            expressions: rhs,
        };
        // Unused!
        let left = SelectedExpressions::default();

        let connection = Connection {
            id: 0,
            left: &left,
            right: &right,
            kind: ConnectionKind::Permutation,
            multiplicity_column: None,
        };

        let machine_parts = MachineParts::new(
            &fixed_data,
            [(0, connection)].into_iter().collect(),
            retained_identities,
            witnesses_by_name.values().copied().collect(),
            // No prover functions
            Vec::new(),
        );

        let processor = BlockMachineProcessor {
            fixed_data: &fixed_data,
            machine_parts,
            block_size,
            latch_row,
        };

        let known_values = BitVec::from_iter(
            input_names
                .iter()
                .map(|_| true)
                .chain(output_names.iter().map(|_| false)),
        );

        processor.generate_code(0, known_values)
    }

    #[test]
    fn add() {
        let input = "
        namespace Add(256);
            col witness sel, a, b, c;
            c = a + b;
        ";
        let code =
            generate_for_block_machine(input, 1, 0, "Add::sel", &["Add::a", "Add::b"], &["Add::c"]);
        assert_eq!(
            format_code(&code.unwrap()),
            "Add::sel[0] = 1;
Add::a[0] = params[0];
Add::b[0] = params[1];
Add::c[0] = (Add::a[0] + Add::b[0]);
params[2] = Add::c[0];"
        );
    }

    #[test]
    fn poseidon() {
        // Copied from the optimized PIL of the PoseidonGL std test.
        let input = "
        namespace main_poseidon(256);
            let FULL_ROUNDS: int = 8_int;
            let PARTIAL_ROUNDS: int = 22_int;
            let ROWS_PER_HASH: int = main_poseidon::FULL_ROUNDS + main_poseidon::PARTIAL_ROUNDS + 1_int;
            col fixed FIRSTBLOCK(i) { if i % main_poseidon::ROWS_PER_HASH == 0_int { 1_fe } else { 0_fe } };
            col fixed LASTBLOCK(i) { if i % main_poseidon::ROWS_PER_HASH == main_poseidon::ROWS_PER_HASH - 1_int { 1_fe } else { 0_fe } };
            col fixed LAST = [0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe, 1_fe]* + [1_fe];
            col fixed PARTIAL = [0_fe, 0_fe, 0_fe, 0_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 1_fe, 0_fe, 0_fe, 0_fe, 0_fe, 0_fe]*;
            col fixed C_0 = [13080132714287612933_fe, 9667108687426275457_fe, 16859897325061800066_fe, 10567510598607410195_fe, 4378616569090929672_fe, 8156487614120951180_fe, 11073536380651186235_fe, 16970959813722173256_fe, 8167785008538063246_fe, 15919951556166196935_fe, 15021242795466053388_fe, 3505040783153922951_fe, 1558644089185031256_fe, 6502946837278398021_fe, 8597377839806076919_fe, 17999926471875633100_fe, 885298637936952595_fe, 15952065508715623490_fe, 216040220732135364_fe, 4397422800601932505_fe, 16761509772042181939_fe, 17070233710126619765_fe, 10376377187857634245_fe, 16001900718237913960_fe, 5575990058472514138_fe, 1475161295215894444_fe, 5142217010456550622_fe, 16645869274577729720_fe, 8927746344866569756_fe, 17564372683613562171_fe, 0_fe]*;
            col fixed C_1 = [8594738767457295063_fe, 6470857420712283733_fe, 17685474420222222349_fe, 8135543733717919110_fe, 3334807502817538491_fe, 10615269510047010719_fe, 4866839313097607757_fe, 15735726858241466429_fe, 9483259819397403968_fe, 4423540216573360915_fe, 3802990509227527157_fe, 3710332827435113697_fe, 4074089203264759305_fe, 15816362857667988792_fe, 9704018824195918000_fe, 635992114476018166_fe, 541790758138118921_fe, 15571300830419767248_fe, 14252611488623712688_fe, 11285062031581972327_fe, 6688821660695954082_fe, 6915716851370550800_fe, 13344930747504284997_fe, 5548469743008097574_fe, 2751301609188252989_fe, 7999197814297036636_fe, 1775580461722730120_fe, 8039205965509554440_fe, 11802068403177695792_fe, 4664015225343144418_fe, 0_fe]*;
            col fixed C_2 = [12896916465481390516_fe, 14103331940138337652_fe, 17858764734618734949_fe, 116353493081713692_fe, 8019184735943344966_fe, 12489426404754222075_fe, 13118391689513956636_fe, 10347018221892268419_fe, 954550221664291548_fe, 16317664700341473511_fe, 4665459515680145682_fe, 15414874040873320221_fe, 2522268501749395707_fe, 12997958454165692924_fe, 12763288618765762688_fe, 17205047318256576347_fe, 5985203084790372993_fe, 17259785660502616862_fe, 9543395466794536974_fe, 7309354640676468207_fe, 12083434295263160416_fe, 9505009849073026581_fe, 11579281865160153596_fe, 14584404916672178680_fe, 6478598528223547074_fe, 2984233088665867938_fe, 161694268822794344_fe, 4788586935019371140_fe, 157833420806751556_fe, 6133721340680280128_fe, 0_fe]*;
            col fixed C_3 = [1109962092811921367_fe, 11854816473550292865_fe, 9410011022665866671_fe, 8029688163494945618_fe, 2395043908812246395_fe, 5055279340069995710_fe, 14527674973762312380_fe, 12195545878449322889_fe, 10339565171024313256_fe, 4723997214951767765_fe, 13165553315407675603_fe, 8602547649919482301_fe, 3414760436185256196_fe, 5314892854495903792_fe, 17249257732622847695_fe, 17384900867876315312_fe, 4685030219775483721_fe, 4298425495274316083_fe, 2714461051639810934_fe, 10457152817239331848_fe, 8540021431714616589_fe, 6422700465081897153_fe, 10300256980048736962_fe, 3396622135873576824_fe, 386565553848556638_fe, 3097746028144832229_fe, 1518963253808031703_fe, 15129007200040077746_fe, 4698875910749767878_fe, 2667022304383014929_fe, 0_fe]*;
            col fixed C_4 = [16216730422861946898_fe, 3498097497301325516_fe, 12495243629579414666_fe, 9003846637224807585_fe, 6558421058331732611_fe, 7231927319780248664_fe, 7612751959265567999_fe, 7423314197114049891_fe, 8651171084286500102_fe, 10098756619006575500_fe, 6496364397926233172_fe, 13971349938398812007_fe, 17420887529146466921_fe, 15533907063555687782_fe, 1998710993415069759_fe, 16484825562915784226_fe, 1411106851304815020_fe, 9023601070579319352_fe, 2588317208781407279_fe, 8855911538863247046_fe, 6891616215679974226_fe, 17977653991560529185_fe, 378765236515040565_fe, 7861729246871155992_fe, 9417729078939938713_fe, 8849530863480031517_fe, 16475258091652710137_fe, 2055561615223771341_fe, 1616722774788291698_fe, 12316557761857340230_fe, 0_fe]*;
            col fixed C_5 = [10137062673499593713_fe, 7947235692523864220_fe, 12416945298171515742_fe, 7052445132467233849_fe, 11735894060727326369_fe, 2602078848106763799_fe, 6808090907814178161_fe, 14908016116973904153_fe, 16974445528003515956_fe, 3223149401237667964_fe, 12800832566287577810_fe, 187239246702636066_fe, 2817020417938125001_fe, 12312015675698548715_fe, 923759906393011543_fe, 16694130609036138894_fe, 11290732479954096478_fe, 7353589709321807492_fe, 15458529123534594916_fe, 4301853449821814398_fe, 10229217098454812721_fe, 5800870252836247255_fe, 11412420941557253424_fe, 16112271126908045545_fe, 15204315939835727483_fe, 7464920943249009773_fe, 119575899007375159_fe, 4149731103701412892_fe, 3990951895163748090_fe, 10375614850625292317_fe, 0_fe]*;
            col fixed C_6 = [15292064466732465823_fe, 11110078701231901946_fe, 5776666812364270983_fe, 9645665432288852853_fe, 8143540538889204488_fe, 12445944369334781425_fe, 6899703779492644997_fe, 5840340122527363265_fe, 15104530047940621190_fe, 6870494874300767682_fe, 9737592377590267426_fe, 12886019973971254144_fe, 16538346563888261485_fe, 14140016464013350248_fe, 1271051229666811593_fe, 10575069350371260875_fe, 208280581124868513_fe, 2988848909076209475_fe, 15748417817551040856_fe, 13001502396339103326_fe, 3292165387203778711_fe, 12096124733159345520_fe, 12931662470734252786_fe, 16988163966860016012_fe, 14942015033780606261_fe, 3802996844641460514_fe, 1275863735937973999_fe, 10268130195734144189_fe, 16758609224720795472_fe, 8141542666379135068_fe, 0_fe]*;
            col fixed C_7 = [17255573294985989181_fe, 16384314112672821048_fe, 6314421662864060481_fe, 5446430061030868787_fe, 5991753489563751169_fe, 3978905923892496205_fe, 3664666286336986826_fe, 17740311462440614128_fe, 103271880867179718_fe, 2902095711130291898_fe, 8687131091302514939_fe, 4512274763990493707_fe, 5592270336833998770_fe, 16325589062962838690_fe, 17822362132088738077_fe, 8330575162062887277_fe, 10979018648467968495_fe, 10439527789422046135_fe, 16414455697114422951_fe, 10218424535115580246_fe, 6090113424998243490_fe, 7679273623392321940_fe, 43018908376346374_fe, 273641680619529493_fe, 18369423901636582012_fe, 6284458522545927646_fe, 16539412514520642374_fe, 13406631635880074708_fe, 3045571693290741477_fe, 9185476451083834432_fe, 0_fe]*;
            col fixed C_8 = [14827154241873003558_fe, 15404405912655775739_fe, 7402742471423223171_fe, 16770910634346036823_fe, 12235918791502088007_fe, 16711272944329818038_fe, 783179505424462608_fe, 815306421953744623_fe, 14654666245504492663_fe, 7159372652788439733_fe, 1488200421755445892_fe, 2986635507805503192_fe, 16876602064684906232_fe, 6796145646370327654_fe, 11797234543722669271_fe, 6212375704691932880_fe, 8600643745023338215_fe, 6097734044161429459_fe, 13378164466674639511_fe, 8628244713920681895_fe, 13431780521962358660_fe, 17835783910585744964_fe, 3589810689190160071_fe, 15222677154027327363_fe, 4715338437538604447_fe, 2307388003445002779_fe, 2303365191438051950_fe, 11429218277824986203_fe, 9281634245289836419_fe, 4991072365274649547_fe, 0_fe]*;
            col fixed C_9 = [2846171647972703231_fe, 14077880830714445579_fe, 982536713192432718_fe, 17708360571433944729_fe, 2880312033702687139_fe, 10439032361227108922_fe, 8990689241814097697_fe, 17456357368219253949_fe, 12445769555936887967_fe, 11500508372997952671_fe, 11004377668730991641_fe, 2315252455709119454_fe, 1793025614521516343_fe, 1168753512742361735_fe, 5864538787265942447_fe, 15965138197626618226_fe, 3477453626867126061_fe, 1113429873817861476_fe, 13894319928411294675_fe, 17410423622514037261_fe, 6061081364215809883_fe, 2478664878205754377_fe, 4688229274750659741_fe, 4070328078309830604_fe, 6840590980607806319_fe, 4461479354745457623_fe, 6435126839960916075_fe, 15773968030812198565_fe, 13517688176723875370_fe, 17398204971778820365_fe, 0_fe]*;
            col fixed C_10 = [16246264663680317601_fe, 9555554662709218279_fe, 17321168865775127905_fe, 4661556288322237631_fe, 18224748115308382355_fe, 15110119871725214866_fe, 9646603555412825679_fe, 6982651076559329072_fe, 11250582358051997490_fe, 13348148181479462670_fe, 13516338734600228410_fe, 12537995864054210246_fe, 2178510518148748532_fe, 4100789820704709368_fe, 15975583211110506970_fe, 14285453069600046939_fe, 6428436309340258604_fe, 1639063372386966591_fe, 5032680892090751540_fe, 14080683768439215375_fe, 16792066504222214142_fe, 1720314468413114967_fe, 13688957436484306091_fe, 13520458500363296391_fe, 5535471161490539014_fe, 1649739722664588460_fe, 17794599201026020053_fe, 16050275277550506872_fe, 7961395585333219380_fe, 16127888338958422584_fe, 0_fe]*;
            col fixed C_11 = [14214208087951879286_fe, 13859595358210603949_fe, 2934354895005980211_fe, 11977051899316327985_fe, 18070411013125314165_fe, 821141790655890946_fe, 7351246026167205041_fe, 11970987324614963868_fe, 6730977207490590241_fe, 12729401155983882093_fe, 2953581820660217936_fe, 2039491936479859267_fe, 2726440714374752509_fe, 15947554381540469177_fe, 7258516085733671960_fe, 10005163510208402517_fe, 5695415667275657934_fe, 7863102812716788759_fe, 17201338494743078916_fe, 11453161143447188100_fe, 16134314044798124799_fe, 10376757819003248056_fe, 11424740943016984272_fe, 8235111705801363015_fe, 5341328005359029952_fe, 3008391274160432867_fe, 13847097589277840330_fe, 11858586752031736643_fe, 1606574359105691080_fe, 13586792051317758204_fe, 0_fe]*;
            col witness state[12];
            col witness output[4];
            col witness x3[12];
            main_poseidon::x3[0] = (main_poseidon::state[0] + main_poseidon::C_0) * (main_poseidon::state[0] + main_poseidon::C_0) * (main_poseidon::state[0] + main_poseidon::C_0);
            main_poseidon::x3[1] = (main_poseidon::state[1] + main_poseidon::C_1) * (main_poseidon::state[1] + main_poseidon::C_1) * (main_poseidon::state[1] + main_poseidon::C_1);
            main_poseidon::x3[2] = (main_poseidon::state[2] + main_poseidon::C_2) * (main_poseidon::state[2] + main_poseidon::C_2) * (main_poseidon::state[2] + main_poseidon::C_2);
            main_poseidon::x3[3] = (main_poseidon::state[3] + main_poseidon::C_3) * (main_poseidon::state[3] + main_poseidon::C_3) * (main_poseidon::state[3] + main_poseidon::C_3);
            main_poseidon::x3[4] = (main_poseidon::state[4] + main_poseidon::C_4) * (main_poseidon::state[4] + main_poseidon::C_4) * (main_poseidon::state[4] + main_poseidon::C_4);
            main_poseidon::x3[5] = (main_poseidon::state[5] + main_poseidon::C_5) * (main_poseidon::state[5] + main_poseidon::C_5) * (main_poseidon::state[5] + main_poseidon::C_5);
            main_poseidon::x3[6] = (main_poseidon::state[6] + main_poseidon::C_6) * (main_poseidon::state[6] + main_poseidon::C_6) * (main_poseidon::state[6] + main_poseidon::C_6);
            main_poseidon::x3[7] = (main_poseidon::state[7] + main_poseidon::C_7) * (main_poseidon::state[7] + main_poseidon::C_7) * (main_poseidon::state[7] + main_poseidon::C_7);
            main_poseidon::x3[8] = (main_poseidon::state[8] + main_poseidon::C_8) * (main_poseidon::state[8] + main_poseidon::C_8) * (main_poseidon::state[8] + main_poseidon::C_8);
            main_poseidon::x3[9] = (main_poseidon::state[9] + main_poseidon::C_9) * (main_poseidon::state[9] + main_poseidon::C_9) * (main_poseidon::state[9] + main_poseidon::C_9);
            main_poseidon::x3[10] = (main_poseidon::state[10] + main_poseidon::C_10) * (main_poseidon::state[10] + main_poseidon::C_10) * (main_poseidon::state[10] + main_poseidon::C_10);
            main_poseidon::x3[11] = (main_poseidon::state[11] + main_poseidon::C_11) * (main_poseidon::state[11] + main_poseidon::C_11) * (main_poseidon::state[11] + main_poseidon::C_11);
            col witness x7[12];
            main_poseidon::x7[0] = main_poseidon::x3[0] * main_poseidon::x3[0] * (main_poseidon::state[0] + main_poseidon::C_0);
            main_poseidon::x7[1] = main_poseidon::x3[1] * main_poseidon::x3[1] * (main_poseidon::state[1] + main_poseidon::C_1);
            main_poseidon::x7[2] = main_poseidon::x3[2] * main_poseidon::x3[2] * (main_poseidon::state[2] + main_poseidon::C_2);
            main_poseidon::x7[3] = main_poseidon::x3[3] * main_poseidon::x3[3] * (main_poseidon::state[3] + main_poseidon::C_3);
            main_poseidon::x7[4] = main_poseidon::x3[4] * main_poseidon::x3[4] * (main_poseidon::state[4] + main_poseidon::C_4);
            main_poseidon::x7[5] = main_poseidon::x3[5] * main_poseidon::x3[5] * (main_poseidon::state[5] + main_poseidon::C_5);
            main_poseidon::x7[6] = main_poseidon::x3[6] * main_poseidon::x3[6] * (main_poseidon::state[6] + main_poseidon::C_6);
            main_poseidon::x7[7] = main_poseidon::x3[7] * main_poseidon::x3[7] * (main_poseidon::state[7] + main_poseidon::C_7);
            main_poseidon::x7[8] = main_poseidon::x3[8] * main_poseidon::x3[8] * (main_poseidon::state[8] + main_poseidon::C_8);
            main_poseidon::x7[9] = main_poseidon::x3[9] * main_poseidon::x3[9] * (main_poseidon::state[9] + main_poseidon::C_9);
            main_poseidon::x7[10] = main_poseidon::x3[10] * main_poseidon::x3[10] * (main_poseidon::state[10] + main_poseidon::C_10);
            main_poseidon::x7[11] = main_poseidon::x3[11] * main_poseidon::x3[11] * (main_poseidon::state[11] + main_poseidon::C_11);
            (main_poseidon::state[0]' - (25 * main_poseidon::x7[0] + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[1]' - (20 * main_poseidon::x7[0] + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[2]' - (34 * main_poseidon::x7[0] + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[3]' - (18 * main_poseidon::x7[0] + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[4]' - (39 * main_poseidon::x7[0] + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[5]' - (13 * main_poseidon::x7[0] + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[6]' - (13 * main_poseidon::x7[0] + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[7]' - (28 * main_poseidon::x7[0] + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[8]' - (2 * main_poseidon::x7[0] + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[9]' - (16 * main_poseidon::x7[0] + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[10]' - (41 * main_poseidon::x7[0] + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 15 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::state[11]' - (15 * main_poseidon::x7[0] + 41 * (main_poseidon::PARTIAL * (main_poseidon::state[1] + main_poseidon::C_1 - main_poseidon::x7[1]) + main_poseidon::x7[1]) + 16 * (main_poseidon::PARTIAL * (main_poseidon::state[2] + main_poseidon::C_2 - main_poseidon::x7[2]) + main_poseidon::x7[2]) + 2 * (main_poseidon::PARTIAL * (main_poseidon::state[3] + main_poseidon::C_3 - main_poseidon::x7[3]) + main_poseidon::x7[3]) + 28 * (main_poseidon::PARTIAL * (main_poseidon::state[4] + main_poseidon::C_4 - main_poseidon::x7[4]) + main_poseidon::x7[4]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[5] + main_poseidon::C_5 - main_poseidon::x7[5]) + main_poseidon::x7[5]) + 13 * (main_poseidon::PARTIAL * (main_poseidon::state[6] + main_poseidon::C_6 - main_poseidon::x7[6]) + main_poseidon::x7[6]) + 39 * (main_poseidon::PARTIAL * (main_poseidon::state[7] + main_poseidon::C_7 - main_poseidon::x7[7]) + main_poseidon::x7[7]) + 18 * (main_poseidon::PARTIAL * (main_poseidon::state[8] + main_poseidon::C_8 - main_poseidon::x7[8]) + main_poseidon::x7[8]) + 34 * (main_poseidon::PARTIAL * (main_poseidon::state[9] + main_poseidon::C_9 - main_poseidon::x7[9]) + main_poseidon::x7[9]) + 20 * (main_poseidon::PARTIAL * (main_poseidon::state[10] + main_poseidon::C_10 - main_poseidon::x7[10]) + main_poseidon::x7[10]) + 17 * (main_poseidon::PARTIAL * (main_poseidon::state[11] + main_poseidon::C_11 - main_poseidon::x7[11]) + main_poseidon::x7[11]))) * (1 - main_poseidon::LAST) = 0;
            main_poseidon::LASTBLOCK * (main_poseidon::output[0] - main_poseidon::state[0]) = 0;
            main_poseidon::LASTBLOCK * (main_poseidon::output[1] - main_poseidon::state[1]) = 0;
            main_poseidon::LASTBLOCK * (main_poseidon::output[2] - main_poseidon::state[2]) = 0;
            main_poseidon::LASTBLOCK * (main_poseidon::output[3] - main_poseidon::state[3]) = 0;
            (main_poseidon::output[0]' - main_poseidon::output[0]) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::output[1]' - main_poseidon::output[1]) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::output[2]' - main_poseidon::output[2]) * (1 - main_poseidon::LAST) = 0;
            (main_poseidon::output[3]' - main_poseidon::output[3]) * (1 - main_poseidon::LAST) = 0;
            col witness sel[1];
            main_poseidon::sel[0] * (1 - main_poseidon::sel[0]) = 0;
        ";
        generate_for_block_machine(
            input,
            31,
            0,
            "main_poseidon::sel[0]",
            &[
                "main_poseidon::state[0]",
                "main_poseidon::state[1]",
                "main_poseidon::state[2]",
                "main_poseidon::state[3]",
                "main_poseidon::state[4]",
                "main_poseidon::state[5]",
                "main_poseidon::state[6]",
                "main_poseidon::state[7]",
                "main_poseidon::state[8]",
                "main_poseidon::state[9]",
                "main_poseidon::state[10]",
                "main_poseidon::state[11]",
            ],
            &[
                "main_poseidon::output[0]",
                "main_poseidon::output[1]",
                "main_poseidon::output[2]",
                "main_poseidon::output[3]",
            ],
        )
        .unwrap();
    }
}
