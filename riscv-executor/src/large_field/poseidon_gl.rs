use powdr_number::FieldElement;

#[rustfmt::skip]
const ROUND_CONSTANTS: [[u64; 30]; 12] = [
    [0xb585f766f2144405, 0x86287821f722c881, 0xe9fa634a21de0082, 0x92a756e67e2b9413, 0x3cc3f892184df408, 0x7131aa45268d7d8c, 0x99ad1aab0814283b, 0xeb84f608da56ef48, 0x7159cd30c3ac118e, 0xdcef0797c2b69ec7, 0xd0762cbc8ca6570c, 0x30a4680593258387, 0x15a16a8a8322d458, 0x5a3f1bb1c53a9645, 0x775005982d74d7f7, 0xf9cc95c22b4c1fcc, 0xc49366bb25e8513, 0xdd611f1000c17442, 0x2ff876fa5ef97c4, 0x3d06c8bd1514e2d9, 0xe89cd854d5d01d33, 0xece5a71e0cfedc75, 0x90004c1371b893c5, 0xde122bebe9a39368, 0x4d61e56a525d225a, 0x1478d361dbbf9fac, 0x475cd3205a3bdcde, 0xe70201e960cb78b8, 0x7be5b9ffda905e1c, 0xf3c12fe54d5c653b],
    [0x7746a55f43921ad7, 0x59cd1a8a41c18e55, 0xf56f6d48959a600d, 0x70e741ebfee96586, 0x2e479dc157bf31bb, 0x9351036095630f9f, 0x438a7c91d416ca4d, 0xda608834c40e603d, 0x839b4e8fafead540, 0x3d639263da827b13, 0x34c6efb812b04bf5, 0x337dc00c61bd9ce1, 0x388a128b7fd9a609, 0xdb7f023869fb8d38, 0x86ab99b4dde6c8b0, 0x8d37f755f4ae9f6, 0x784d3d2f1698309, 0xd8185f9adfea4fd0, 0xc5cb72a2a51159b0, 0x9c9c98207cb10767, 0x5cd377dc8bb882a2, 0x5ff98fd5d51fe610, 0xb932b7cf752e5545, 0x4d001fd58f002526, 0x262e963c8da05d3d, 0x6f02dc07d141875c, 0x18a42105c31b7e88, 0x6f90ff3b6a65f108, 0xa3c95eaec244aa30, 0x40b9e922ed9771e2],
    [0xb2fb0d31cee799b4, 0xc3b919ad495dc574, 0xf7d713e806391165, 0x19d5ee2af82ec1c, 0x6f49de07a6234346, 0xad535b24afc26bfb, 0xb60de3bcc5ea751c, 0x8f97fe408061f183, 0xd3f3e5e82920adc, 0xe273fd971bc8d0e7, 0x40bf0ab5fa14c112, 0xd5eca244c7a4ff1d, 0x2300e5d6baedf0fb, 0xb462065911d4e1fc, 0xb1204f603f51c080, 0xeec49b613478675b, 0x530fb67ea1809a81, 0xef87139ca9a3ab1e, 0x8470f39d2d5c900e, 0x65700b51aedfb5ef, 0xa7b0fb7883eee860, 0x83e8941918964615, 0xa0b1df81b6fe59fc, 0xca6637000eb4a9f8, 0x59e89b094d220ec2, 0x296a202ed8e556a2, 0x23e7414af663068, 0x42747a7245e7fa84, 0x230bca8f4df0544, 0x551f5b0fbe7b1840],
    [0xf6760a4803427d7, 0xa484c4c5ef6a0781, 0x8297132b32825daf, 0x6f6f2ed772466352, 0x213ce7bede378d7b, 0x4627f5c6993e44be, 0xc99cab6aef6f58bc, 0xa93f485c96f37b89, 0x8f7d83bddee7bba8, 0x418f02702d227ed5, 0xb6b570fc7c5740d3, 0x7762638264d279bd, 0x2f63aa8647e15104, 0x49c24ae4437d8030, 0xef61ac8470250ecf, 0xf143933aed25e0b0, 0x410492299bb01f49, 0x3ba71336c34ee133, 0x25abb3f1d39fcb76, 0x911f451539869408, 0x7684403ec392950d, 0x5922040b47f150c1, 0x8ef1dd26770af2c2, 0x2f2339d624f91f78, 0x55d5b52b78b9c5e, 0x2afd67999bf32ee5, 0x15147108121967d7, 0xd1f507e43ab749b2, 0x4135c2bebfe148c6, 0x25032aa7c4cb1811],
    [0xe10d666650f4e012, 0x308bbd23dc5416cc, 0xad6805e0e30b2c8a, 0x7cf416cfe7e14ca1, 0x5b0431345d4dea83, 0x645cf794b8f1cc58, 0x69a5ed92a72ee4ff, 0x6704e8ee8f18d563, 0x780f2243ea071d06, 0x8c25fda3b503038c, 0x5a27b9002de33454, 0xc1e434bedeefd767, 0xf1c36ce86ecec269, 0xd793862c112b0566, 0x1bbcd90f132c603f, 0xe4c5dd8255dfc622, 0x139542347424b9ac, 0x7d3a455d56b70238, 0x23eb8cc9b372442f, 0x7ae6849fbc3a0ec6, 0x5fa3f06f4fed3b52, 0xf97d750e3dd94521, 0x541a4f9cfbeed35, 0x6d1a7918c80df518, 0x82b27eb33514ef99, 0x7acfd96efa95491d, 0xe4a3dff1d7d6fef9, 0x1c86d265f15750cd, 0x166fc0cc438a3c72, 0xaaed34074b164346],
    [0x8cae14cb07d09bf1, 0x6e4a40c18f30c09c, 0xac51d9f5fcf8535e, 0x61df517b86a46439, 0xa2de45780344d6a1, 0x241c70ed0af61617, 0x5e7b329c1ed4ad71, 0xcee3e9ac1e072119, 0xeb915845f3de1634, 0x2cbaed4daec8c07c, 0xb1a5b165b6d2b2d2, 0x299351a53b8ec22, 0x27181125183970c9, 0xaadd1106730d8feb, 0xcd1dabd964db557, 0xe7ad7756f193198e, 0x9cb0bd5ea1a1115e, 0x660d32e130182684, 0xd687ba55c64f6364, 0x3bb340eba06afe7e, 0x8df57ac11bc04831, 0x5080d4c2b86f56d7, 0x9e61106178bfc530, 0xdf9a4939342308e9, 0xd30094ca96b7ce7b, 0x6798ba0c0abb2c6d, 0x1a8d1a588085737, 0x3996ce73dd832c1c, 0x3762b59a8ae83efa, 0x8ffd96bbf9c9c81d],
    [0xd438539c95f63e9f, 0x9a2eedb70d8f8cfa, 0x502ad7dc18c2ad87, 0x85dc499b11d77b75, 0x7103aaf94a7bf308, 0xacb8e076647905f1, 0x5fc0ac0800144885, 0x510d0e65e2b470c1, 0xd19e120d26b6f386, 0x5f58e6afcdd6ddc2, 0x8722e0ace9d1be22, 0xb2d456e4ad251b80, 0xe584029370dca96d, 0xc43b6e0e97b0d568, 0x11a3ae5beb9d1ec9, 0x92c2318b87fff9cb, 0x2e3f615c38f49a1, 0x297a863f48cd1f43, 0xda8d9e90fd8ff158, 0xb46e9d8b682ea65e, 0x2db01efa1e1e1897, 0xa7de115b56c78d70, 0xb3767e80935d8af2, 0xebc2151ee6c8398c, 0xcf5cb381cd0a1535, 0x34c6f57b26c92122, 0x11b4c74eda62beef, 0x8e7fba02983224bd, 0xe8928a4c89114750, 0x70fc91eb5937085c],
    [0xef781c7ce35b4c3d, 0xe360c6e0ae486f38, 0x57a1550c110b3041, 0x4b959b48b9c10733, 0x5326fc0d97279301, 0x3737e9db4c4f474d, 0x32db829239774eca, 0xf6323f486b9038f0, 0x16ee53a7e5fecc6, 0x284650ac5e1b0eba, 0x788ee3b37e5680fb, 0x3e9ed1fda49cea0b, 0x4d9bbc3e02f1cfb2, 0xe29024c18ee6fca2, 0xf755bfeea585d11d, 0x739c25f8fd73596d, 0x985d4f4a9c5291ef, 0x90e0a736a751ebb7, 0xe3cbdc7d2fe45ea7, 0x8dcf22f9a3b34356, 0x54846de4aadb9ca2, 0x6a9242ac87538194, 0x98d5782065af06, 0x3cc2ba8a1116515, 0xfeed4db6919e5a7c, 0x5736e1bad206b5de, 0xe587cc0d69a73346, 0xba0dec7103255dd4, 0x2a440b51a4945ee5, 0x7f795e2a5f915440],
    [0xcdc4a239b0c44426, 0xd5c7718fbfc647fb, 0x66bbd30e6ce0e583, 0xe8be3e5da8043e57, 0xa9ceb74fec024747, 0xe7ea5e33e75fffb6, 0xade699c5830f310, 0xb508cdeffa5ceef, 0xcb5fd54e7933e477, 0x635b337ee819dab5, 0x14a726661551e284, 0x2972a92ba450bed8, 0xea35bc29692af6f8, 0x5e50c27535b88c66, 0xa3b83250268ea4d7, 0x5636cac9f16dfed0, 0x775b9feafdcd26e7, 0x549f80ce550c4fd3, 0xb9a8c9b3aee52297, 0x77bdaeda586257a7, 0xba6745385893c784, 0xf7856ef7f9173e44, 0x31d191cd5c1466c7, 0xd341d037e840cf83, 0x41703f53753be59f, 0x20057d2a0056521b, 0x1ff7327017aa2a6e, 0x9e9cbd781628fc5b, 0x80cefd2b7d99ff83, 0x4543d9df5476d3cb],
    [0x277fa208bf337bff, 0xc35eae071903ff0b, 0xda2abef589d644e, 0xf5c0bc1de6da8699, 0x27f8ec88bb21b1a3, 0x90dee49fc9bfc23a, 0x7cc5583b10415f21, 0xf2417089e4fb3cbd, 0xacb8417879fd449f, 0x9f9a036ed4f2d49f, 0x98b7672f9ef3b419, 0x20216dd77be493de, 0x18e21b4beabb4137, 0x10383f20a4ff9a87, 0x516306f4927c93af, 0xdd8f909a938e0172, 0x304265a6384f0f2d, 0xf73b2922f38bd64, 0xc0d28a5c10960bd3, 0xf19e400a5104d20d, 0x541d496344d2c75b, 0x2265fc92feb0dc09, 0x410fefafa319ac9d, 0x387cb5d25af4afcc, 0x5eeea940fcde8b6f, 0x3dea5bd5d0578bd7, 0x594e29c42473d06b, 0xdae8645996edd6a5, 0xbb9879c6e61fd62a, 0xf172d73e004fc90d],
    [0xe17653a29da578a1, 0x849c2656969c4be7, 0xf061274fdb150d61, 0x40b12cbf09ef74bf, 0xfceb4fda1ded0893, 0xd1b1edf76bc09c92, 0x85df9ed2e166d64f, 0x60e75c2890d15730, 0x9c22190be7f74732, 0xb93e260cae5c170e, 0xbb93ae776bb30e3a, 0xadffe8cf28449ec6, 0x1e3b9fc625b554f4, 0x38e8ee9d71a45af8, 0xddb4ac49c9efa1da, 0xc6401fe115063f5b, 0x593664c39773012c, 0x16bf1f73fb7a9c3f, 0x45d7ac9b68f71a34, 0xc368a348e46d950f, 0xe909678474e687fe, 0x17dfc8e4f7ba8a57, 0xbdf8f242e316c4ab, 0xbba2515f22909e87, 0x4cd1f1b175100206, 0x16e50d897d4634ac, 0xf6f31db1899b12d5, 0xdebe0853b1a1d378, 0x6e7c8f1a84265034, 0xdfd1c4febcc81238],
    [0xc54302f225db2c76, 0xc0572c8c08cbbbad, 0x28b8ec3ae9c29633, 0xa637093ecb2ad631, 0xfac6ff1346a41675, 0xb65481ba645c602, 0x6604df4fee32bcb1, 0xa6217d8bf660f29c, 0x5d693c1ba3ba3621, 0xb0a7eae879ddb76d, 0x28fd3b046380f850, 0x1c4dbb1c4c27d243, 0x25d64362697828fd, 0xdd5118375bf1a9b9, 0x64bb6dec369d4418, 0x8ad97b33f1ac1455, 0x4f0a2e5fb028f2ce, 0x6d1f5a59005bec17, 0xeeb76e397069e804, 0x9ef1cd60e679f284, 0xdfe89923f6c9c2ff, 0x9001a64209f21db8, 0x9e8cd55b57637ed0, 0x7248fe7705f38e47, 0x4a20358574454ec0, 0x29bff3ecb9b7a6e3, 0xc02ac5e47312d3ca, 0xa49229d24d014343, 0x164bb2de1bbeddc8, 0xbc8dfb627fe558fc],
];

const MDS_MATRIX: [[u64; 12]; 12] = [
    [25, 15, 41, 16, 2, 28, 13, 13, 39, 18, 34, 20],
    [20, 17, 15, 41, 16, 2, 28, 13, 13, 39, 18, 34],
    [34, 20, 17, 15, 41, 16, 2, 28, 13, 13, 39, 18],
    [18, 34, 20, 17, 15, 41, 16, 2, 28, 13, 13, 39],
    [39, 18, 34, 20, 17, 15, 41, 16, 2, 28, 13, 13],
    [13, 39, 18, 34, 20, 17, 15, 41, 16, 2, 28, 13],
    [13, 13, 39, 18, 34, 20, 17, 15, 41, 16, 2, 28],
    [28, 13, 13, 39, 18, 34, 20, 17, 15, 41, 16, 2],
    [2, 28, 13, 13, 39, 18, 34, 20, 17, 15, 41, 16],
    [16, 2, 28, 13, 13, 39, 18, 34, 20, 17, 15, 41],
    [41, 16, 2, 28, 13, 13, 39, 18, 34, 20, 17, 15],
    [15, 41, 16, 2, 28, 13, 13, 39, 18, 34, 20, 17],
];

/// Naive implementation of the Poseidon Hash function on the Goldilocks field.
/// Ported from:
/// - https://github.com/0xPolygonHermez/zkevm-proverjs/blob/main/pil/poseidong.pil
/// - https://github.com/0xPolygonHermez/zkevm-proverjs/blob/main/src/sm/sm_poseidong.js
///
/// It's also equivalent to std::machines::hash::poseidon_gl::PoseidonGL from the Powdr standard library.
pub fn poseidon_gl<F: FieldElement>(inputs: &[F]) -> [F; 4] {
    assert_eq!(inputs.len(), 12);
    let mut state = [F::zero(); 12];
    state.copy_from_slice(inputs);

    for round in 0..30 {
        let is_full = !(4..26).contains(&round);
        for i in 0..12 {
            state[i] += F::from(ROUND_CONSTANTS[i][round]);
        }
        for (i, s) in state.iter_mut().enumerate() {
            if is_full || i == 0 {
                *s = s.pow(7.into());
            }
        }
        let mds_input = state;
        for i in 0..12 {
            let mut tmp = F::zero();
            for (j, &input) in mds_input.iter().enumerate() {
                tmp += input * F::from(MDS_MATRIX[i][j]);
            }
            state[i] = tmp;
        }
    }

    let mut result = [F::zero(); 4];
    result.copy_from_slice(state[0..4].as_ref());
    result
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use powdr_number::{FieldElement, GoldilocksField};

    use super::*;

    fn run_test(inputs: &[u64], expected_output: &[u64]) {
        let inputs = inputs
            .iter()
            .map(|&x| GoldilocksField::from(x))
            .collect_vec();
        let output = poseidon_gl(&inputs);
        let output: [u64; 4] = output.map(|x| x.to_arbitrary_integer().try_into().unwrap());
        assert_eq!(&output, expected_output);
    }

    #[test]
    fn poseidon_gl_function() {
        // See test vectors at:
        // https://github.com/0xPolygonHermez/zkevm-testvectors/blob/main/poseidon/raw-hash.json
        let inputs: Vec<u64> = vec![0; 12];
        let expected = vec![
            4330397376401421145,
            14124799381142128323,
            8742572140681234676,
            14345658006221440202,
        ];
        run_test(&inputs, &expected);

        let inputs: Vec<u64> = vec![1; 12];
        let expected = vec![
            16428316519797902711,
            13351830238340666928,
            682362844289978626,
            12150588177266359240,
        ];
        run_test(&inputs, &expected);

        let minus_one: u64 = 0xffffffff00000001 - 1;
        let inputs: Vec<u64> = vec![minus_one; 12];
        let expected = vec![
            13691089994624172887,
            15662102337790434313,
            14940024623104903507,
            10772674582659927682,
        ];
        run_test(&inputs, &expected);

        let inputs: Vec<u64> = vec![18446744069414584321; 12];
        let expected = vec![
            4330397376401421145,
            14124799381142128323,
            8742572140681234676,
            14345658006221440202,
        ];
        run_test(&inputs, &expected);

        let inputs: Vec<u64> = vec![
            923978,
            235763497586,
            9827635653498,
            112870,
            289273673480943876,
            230295874986745876,
            6254867324987,
            2087,
            0,
            0,
            0,
            0,
        ];
        let expected = vec![
            1892171027578617759,
            984732815927439256,
            7866041765487844082,
            8161503938059336191,
        ];
        run_test(&inputs, &expected);
    }
}
