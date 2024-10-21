use std::collections::BTreeMap;

use powdr_riscv_syscalls::Syscall;

use itertools::Itertools;

use crate::code_gen::Register;
use crate::small_field::code_gen::{u32_high, u32_low};

use crate::runtime::{
    parse_function_statement, parse_instruction_declaration, SubMachine, SyscallImpl,
    EXTRA_REG_PREFIX,
};
use crate::RuntimeLibs;

/// RISCV powdr assembly runtime.
/// Determines submachines, instructions and syscalls available to the main machine.
#[derive(Clone)]
pub struct Runtime {
    submachines: BTreeMap<String, SubMachine>,
    syscalls: BTreeMap<Syscall, SyscallImpl>,
}

impl Runtime {
    pub fn new(libs: RuntimeLibs, continuations: bool) -> Self {
        let mut runtime = Runtime::base();
        if libs.poseidon {
            runtime = runtime.with_poseidon(continuations);
        }
        if libs.keccak {
            runtime = runtime.with_keccak();
        }
        if libs.arith {
            runtime = runtime.with_arith();
        }
        runtime
    }

    pub fn base() -> Self {
        let mut r = Runtime {
            submachines: Default::default(),
            syscalls: Default::default(),
        };

        // Base submachines
        // TODO: can/should the memory machine be part of the runtime also?
        r.add_submachine(
            "std::machines::small_field::binary::Binary",
            None,
            "binary",
            vec!["byte_binary"],
            [
                r#"instr and XL, YL, ZH, ZL, WL
                            link ~> (tmp1_h, tmp1_l) = regs.mload(0, XL, STEP)
                            link ~> (tmp2_h, tmp2_l) = regs.mload(0, YL, STEP + 1)
                            link ~> (tmp3_h, tmp3_l) = add_sub.add(tmp2_h, tmp2_l, ZH, ZL)
                            link ~> (tmp4_h, tmp4_l) = binary.and(tmp1_h, tmp1_l, tmp3_h, tmp3_l)
                            link ~> regs.mstore(0, WL, STEP + 3, tmp4_h, tmp4_l);"#,
                r#"instr or XL, YL, ZH, ZL, WL
                            link ~> (tmp1_h, tmp1_l) = regs.mload(0, XL, STEP)
                            link ~> (tmp2_h, tmp2_l) = regs.mload(0, YL, STEP + 1)
                            link ~> (tmp3_h, tmp3_l) = add_sub.add(tmp2_h, tmp2_l, ZH, ZL)
                            link ~> (tmp4_h, tmp4_l) = binary.or(tmp1_h, tmp1_l, tmp3_h, tmp3_l)
                            link ~> regs.mstore(0, WL, STEP + 3, tmp4_h, tmp4_l);"#,
                r#"instr xor XL, YL, ZH, ZL, WL
                            link ~> (tmp1_h, tmp1_l) = regs.mload(0, XL, STEP)
                            link ~> (tmp2_h, tmp2_l) = regs.mload(0, YL, STEP + 1)
                            link ~> (tmp3_h, tmp3_l) = add_sub.add(tmp2_h, tmp2_l, ZH, ZL)
                            link ~> (tmp4_h, tmp4_l) = binary.xor(tmp1_h, tmp1_l, tmp3_h, tmp3_l)
                            link ~> regs.mstore(0, WL, STEP + 3, tmp4_h, tmp4_l);"#,
            ],
            0,
            ["and 0, 0, 0, 0, 0;"],
        );

        r.add_submachine(
            "std::machines::small_field::shift::Shift",
            None,
            "shift",
            vec!["byte_shift"],
            [
                r#"instr shl XL, YL, ZH, ZL, WL
                    link ~> (tmp1_h, tmp1_l) = regs.mload(0, XL, STEP)
                    link ~> (tmp2_h, tmp2_l) = regs.mload(0, YL, STEP)
                    link ~> (tmp3_h, tmp3_l) = add_sub.add(tmp2_h, tmp2_l, ZH, ZL)
                    link ~> (tmp4_l, tmp4_h) = shift.shl(tmp1_l, tmp1_h, tmp3_l)
                    link ~> regs.mstore(0, WL, STEP + 3, tmp4_h, tmp4_l);
"#,
                r#"instr shr XL, YL, ZH, ZL, WL
                    link ~> (tmp1_h, tmp1_l) = regs.mload(0, XL, STEP)
                    link ~> (tmp2_h, tmp2_l) = regs.mload(0, YL, STEP)
                    link ~> (tmp3_h, tmp3_l) = add_sub.add(tmp2_h, tmp2_l, ZH, ZL)
                    link ~> (tmp4_l, tmp4_h) = shift.shr(tmp1_l, tmp1_h, tmp3_l)
                    link ~> regs.mstore(0, WL, STEP + 3, tmp4_h, tmp4_l);
"#,
            ],
            0,
            ["shl 0, 0, 0, 0, 0;"],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::range::Bit2",
            None,
            "bit2",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::range::Bit6",
            None,
            "bit6",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::range::Bit7",
            None,
            "bit7",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::range::Byte",
            None,
            "byte",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::range::Bit12",
            None,
            "bit12",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::range::Byte2",
            None,
            "byte2",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::binary::ByteBinary",
            None,
            "byte_binary",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::small_field::shift::ByteShift",
            None,
            "byte_shift",
            vec![],
            [],
            0,
            [],
        );

        r.add_submachine::<&str, _, _>(
            "std::machines::split::ByteCompare",
            None,
            "byte_compare",
            vec![],
            [],
            0,
            [],
        );

        // Base syscalls
        r.add_syscall(
            // TODO this is a quite inefficient way of getting prover inputs.
            // We need to be able to access the register memory within PIL functions.
            Syscall::Input,
            [
                "query_arg_1_h, query_arg_1_l <== get_reg(10);",
                "query_arg_2_h, query_arg_2_l <== get_reg(11);",
                // TODO fix for BabyBear
                "set_reg 10, 0, ${ std::prelude::Query::Input(std::convert::int(std::prover::eval(query_arg_1_l)), std::convert::int(std::prover::eval(query_arg_2_l))) };",
            ]
        );

        r.add_syscall(
            Syscall::Output,
            // This is using x0 on purpose, because we do not want to introduce
            // nondeterminism with this.
            [
                "query_arg_1_h, query_arg_1_l <== get_reg(10);",
                "query_arg_2_h, query_arg_2_l <== get_reg(11);",
                "set_reg 0, 0, ${ std::prelude::Query::Output(std::convert::int(std::prover::eval(query_arg_1_l)), std::prover::eval(query_arg_2_l)) };"
            ]
        );

        r.add_syscall(Syscall::Halt, ["return;"]);

        r
    }

    fn with_keccak(self) -> Self {
        todo!()
    }

    #[allow(clippy::too_many_arguments)]
    fn add_submachine<S: AsRef<str>, I1: IntoIterator<Item = S>, I2: IntoIterator<Item = S>>(
        &mut self,
        path: &str,
        alias: Option<&str>,
        instance_name: &str,
        arguments: Vec<&str>,
        instructions: I1,
        extra_registers: u8,
        init_call: I2,
    ) {
        let subm = SubMachine {
            path: str::parse(path).expect("invalid submachine path"),
            alias: alias.map(|s| s.to_string()),
            instance_name: instance_name.to_string(),
            arguments: arguments.into_iter().map(|s| s.to_string()).collect(),
            instructions: instructions
                .into_iter()
                .map(|s| parse_instruction_declaration(s.as_ref()))
                .collect(),
            extra_registers,
            init_call: init_call
                .into_iter()
                .map(|s| parse_function_statement(s.as_ref()))
                .collect(),
        };
        assert!(
            self.submachines
                .insert(instance_name.to_string(), subm)
                .is_none(),
            "submachine {instance_name} already present"
        );
    }

    fn add_syscall<S: AsRef<str>, I: IntoIterator<Item = S>>(
        &mut self,
        syscall: Syscall,
        implementation: I,
    ) {
        let implementation = SyscallImpl(
            implementation
                .into_iter()
                .map(|s| parse_function_statement(s.as_ref()))
                .collect(),
        );

        if self.syscalls.insert(syscall, implementation).is_some() {
            panic!("duplicate syscall {syscall}");
        }
    }

    fn with_poseidon(mut self, continuations: bool) -> Self {
        let init_call = if continuations {
            vec![
                "mstore_bootloader 0, 0, 0, 0, 0;",
                "mstore_bootloader 0, 0, 0, 4, 0;",
                "mstore_bootloader 0, 0, 0, 8, 0;",
                "mstore_bootloader 0, 0, 0, 12, 0;",
                "mstore_bootloader 0, 0, 0, 16, 0;",
                "mstore_bootloader 0, 0, 0, 20, 0;",
                "mstore_bootloader 0, 0, 0, 24, 0;",
                "mstore_bootloader 0, 0, 0, 28, 0;",
                "mstore_bootloader 0, 0, 0, 32, 0;",
                "mstore_bootloader 0, 0, 0, 36, 0;",
                "mstore_bootloader 0, 0, 0, 40, 0;",
                "mstore_bootloader 0, 0, 0, 44, 0;",
                "mstore_bootloader 0, 0, 0, 48, 0;",
                "mstore_bootloader 0, 0, 0, 52, 0;",
                "mstore_bootloader 0, 0, 0, 56, 0;",
                "mstore_bootloader 0, 0, 0, 60, 0;",
                "poseidon_bb 0, 0;",
            ]
        } else {
            vec!["poseidon_bb 0, 0;"]
        };
        self.add_submachine(
            "std::machines::hash::poseidon_bb::PoseidonBB",
            None,
            "poseidon_bb",
            vec!["memory"],
            [r#"instr poseidon_bb XL, YL
                    link ~> (tmp1_h, tmp1_l) = regs.mload(XL, STEP)
                    link ~> (tmp2_h, tmp2_l) = regs.mload(YL, STEP + 1)
                    link ~> poseidon_bb.poseidon_permutation(tmp1_h * 2**16 + tmp1_l, tmp2_h * 2**16 + tmp2_l, STEP)
                {
                    // TODO: fix the following for BB

                    // // make sure tmp1_col and tmp2_col are aligned memory addresses
                    // tmp3_col * 4 = tmp1_col,
                    // tmp4_col * 4 = tmp2_col,
                    // // make sure the factors fit in 32 bits
                    // tmp3_col = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000,
                    // tmp4_col = Y_b5 + Y_b6 * 0x100 + Y_b7 * 0x10000 + Y_b8 * 0x1000000
                }
            "#],
            0,
            init_call,
        );

        // The poseidon syscall has a single argument passed on x10, the
        // memory address of the 16 field element input array. Since the memory
        // offset is chosen by LLVM, we assume it's properly aligned.
        let implementation = std::iter::once("poseidon_bb 10, 10;".to_string());

        self.add_syscall(Syscall::PoseidonGL, implementation);
        self
    }

    pub fn has_submachine(&self, name: &str) -> bool {
        self.submachines.contains_key(name)
    }

    fn with_arith(self) -> Self {
        todo!()
    }

    pub fn submachines_init(&self) -> Vec<String> {
        self.submachines
            .values()
            .flat_map(|m| m.init_call.iter())
            .map(|s| s.to_string())
            .collect()
    }

    pub fn submachines_import(&self) -> String {
        self.submachines.values().map(|m| m.import()).join("\n")
    }

    pub fn submachines_declare(&self) -> String {
        self.submachines
            .values()
            .map(|m| m.declaration())
            .join("\n")
    }

    pub fn submachines_instructions(&self) -> Vec<String> {
        self.submachines
            .values()
            .flat_map(|m| m.instructions.iter())
            .map(|s| s.to_string())
            .collect()
    }

    pub fn submachines_extra_registers(&self) -> Vec<String> {
        let count = self
            .submachines
            .values()
            .map(|m| m.extra_registers)
            .max()
            .unwrap_or(0);

        (0..count)
            .map(|i| format!("reg {EXTRA_REG_PREFIX}{i};"))
            .collect()
    }

    pub fn ecall_handler(&self) -> Vec<String> {
        let ecall = [
            "// ecall handler".to_string(),
            "__ecall_handler:".to_string(),
        ]
        .into_iter();

        let jump_table = self.syscalls.keys().map(|s| {
            let s32_h = u32_high(*s as u32);
            let s32_l = u32_low(*s as u32);
            format!("branch_if_diff_equal 5, 0, {s32_h}, {s32_l}, __ecall_handler_{s};",)
        });

        let invalid_handler = ["__invalid_syscall:".to_string(), "fail;".to_string()].into_iter();

        let handlers = self.syscalls.iter().flat_map(|(syscall, implementation)| {
            std::iter::once(format!("__ecall_handler_{syscall}:"))
                .chain(implementation.0.iter().map(|i| i.to_string()))
                .chain([format!("jump_dyn 1, {};", Register::from("tmp1").addr())])
        });

        ecall
            .chain(jump_table)
            .chain(invalid_handler)
            .chain(handlers)
            .chain(std::iter::once("// end of ecall handler".to_string()))
            .collect()
    }
}
