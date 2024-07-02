mod common;

mod instruction_tests {
    use crate::common::verify_riscv_asm_string;
    use powdr_backend::BackendType;
    use powdr_number::GoldilocksField;
    use powdr_riscv::asm::compile;
    use powdr_riscv::Runtime;
    use test_log::test;

    fn run_instruction_test(assembly: &str, name: &str) {
        // Test from ELF path:
        common::verify_riscv_asm_file(file, &Runtime::base(), false);

        // Test from assembly path:
        // TODO Should we create one powdr-asm from all tests or keep them separate?
        let powdr_asm = compile::<GoldilocksField>(
            [(name.to_string(), assembly.to_string())].into(),
            &Runtime::base(),
            false,
        );

        verify_riscv_asm_string::<()>(
            &format!("{name}.asm"),
            &powdr_asm,
            Default::default(),
            None,
            BackendType::EStarkDump,
        );
    }

    include!(concat!(env!("OUT_DIR"), "/instruction_tests.rs"));
}
