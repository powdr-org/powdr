use std::vec;

use itertools::Itertools;
use powdr_isa_utils::SingleDataValue;
use powdr_isa_utils::{escape_label, quote};
use powdr_number::KnownField;

use crate::continuations::bootloader::{bootloader_and_shutdown_routine, bootloader_preamble};

use crate::code_gen::{
    InstructionArgs, MemEntry, Register, RiscVProgram, SourceFileInfo, Statement,
};
use crate::CompilerOptions;

use crate::large_field::runtime::Runtime;

/// Translates a RISC-V program to POWDR ASM
/// with constraints that work for a field >= the Goldilocks modulus.
///
/// Will call each of the methods in the `RiscVProgram` just once.
pub fn translate_program(program: impl RiscVProgram, options: CompilerOptions) -> String {
    let runtime = Runtime::new(options.libs, options.continuations);
    // Do this in a separate function to avoid most of the code being generic on F.
    let (initial_mem, instructions) =
        translate_program_impl(program, options.field, &runtime, options.continuations);

    riscv_machine(
        &runtime,
        &preamble(options.field, &runtime, options.continuations),
        initial_mem,
        instructions,
    )
}

fn translate_program_impl(
    mut program: impl RiscVProgram,
    field: KnownField,
    runtime: &Runtime,
    continuations: bool,
) -> (Vec<String>, Vec<String>) {
    let mut initial_mem = Vec::new();
    let mut data_code = Vec::new();
    for MemEntry { label, addr, value } in program.take_initial_mem() {
        if let Some(label) = label {
            // This is a comment, so we don't need to escape the label.
            let comment = format!(" // data {label}");
            if continuations && !matches!(value, SingleDataValue::LabelReference(_)) {
                &mut initial_mem
            } else {
                &mut data_code
            }
            .push(comment);
        }
        match value {
            SingleDataValue::Value(v) => {
                if continuations {
                    // Instead of generating the data loading code, we store it
                    // in the variable that will be used as the initial memory
                    // snapshot, committed by the bootloader.
                    initial_mem.push(format!("(0x{addr:x}, 0x{v:x})"));
                } else {
                    data_code.push(format!(
                        "set_reg {}, 0x{v:x};",
                        Register::from("tmp2").addr()
                    ));
                    data_code.push(format!(
                        "set_reg {}, 0x{addr:x};",
                        Register::from("tmp1").addr()
                    ));
                    data_code.push(format!(
                        "mstore {}, 0, 0, {};",
                        Register::from("tmp1").addr(),
                        Register::from("tmp2").addr()
                    ));
                }
            }
            SingleDataValue::LabelReference(sym) => {
                // The label value is not known at this point, so we have to
                // load it via code, irrespectively of bootloader availability.
                //
                // TODO should be possible without temporary
                data_code.extend([
                    format!(
                        "load_label {}, {};",
                        Register::from("tmp2").addr(),
                        escape_label(&sym)
                    ),
                    format!("set_reg {}, 0x{addr:x};", Register::from("tmp1").addr()),
                    format!(
                        "mstore {}, 0, 0, {};",
                        Register::from("tmp1").addr(),
                        Register::from("tmp2").addr()
                    ),
                ]);
            }
            SingleDataValue::Offset(_, _) => {
                unimplemented!();
                /*
                object_code.push(format!("addr <=X= 0x{pos:x};"));

                I think this solution should be fine but hard to say without
                an actual code snippet that uses it.

                // TODO should be possible without temporary
                object_code.extend([
                    format!("tmp1 <== load_label({});", escape_label(a)),
                    format!("tmp2 <== load_label({});", escape_label(b)),
                    // TODO check if registers match
                    "mstore wrap(tmp1 - tmp2);".to_string(),
                ]);
                */
            }
        }
    }

    let submachines_init = runtime.submachines_init();
    let bootloader_and_shutdown_routine_lines = if continuations {
        let bootloader_and_shutdown_routine =
            bootloader_and_shutdown_routine(field, &submachines_init);
        log::debug!("Adding Bootloader:\n{}", bootloader_and_shutdown_routine);
        bootloader_and_shutdown_routine
            .split('\n')
            .map(|l| l.to_string())
            .collect::<Vec<_>>()
    } else {
        submachines_init
    };

    let mut statements: Vec<String> = program
        .take_source_files_info()
        .map(
            |SourceFileInfo {
                 id,
                 dir,
                 file: name,
             }| { format!(".debug file {id} {} {};", quote(dir), quote(name)) },
        )
        .chain(bootloader_and_shutdown_routine_lines)
        .collect();
    if !data_code.is_empty() {
        statements.push("jump __data_init, 1;".to_string());
    }
    statements.extend([
        "set_reg 0, 0;".to_string(),
        format!(
            "jump {}, 1;",
            escape_label(program.start_function().as_ref())
        ),
        "return;".to_string(), // This is not "riscv ret", but "return from powdr asm function".
    ]);
    for s in program.take_executable_statements() {
        match s {
            Statement::DebugLoc { file, line, col } => {
                statements.push(format!(".debug loc {file} {line} {col};"))
            }
            Statement::Label(l) => statements.push(format!("{}:", escape_label(l.as_ref()))),
            Statement::Instruction { op, args } => {
                let processed_instr = match process_instruction(op, args) {
                    Ok(s) => s,
                    Err(e) => panic!("Failed to process instruction '{op}'. {e}"),
                };
                statements.extend(processed_instr.into_iter().map(|s| "  ".to_string() + &s))
            }
        }
    }

    if !data_code.is_empty() {
        statements.extend(
            [
                "// This is the data initialization routine.".to_string(),
                "__data_init:".to_string(),
            ]
            .into_iter()
            .chain(data_code)
            .chain([
                "// This is the end of the data initialization routine.".to_string(),
                format!("jump_dyn 1, {};", Register::from("tmp1").addr()),
            ]),
        );
    }
    statements.extend(runtime.ecall_handler());

    (initial_mem, statements)
}

fn riscv_machine(
    runtime: &Runtime,
    preamble: &str,
    initial_memory: Vec<String>,
    program: Vec<String>,
) -> String {
    format!(
        r#"
{}
machine Main with min_degree: {}, max_degree: {} {{
{}

{}

let initial_memory: (int, int)[] = [
{}
];

    function main {{
{}
    }}
}}    
"#,
        runtime.submachines_import(),
        1 << powdr_linker::MIN_DEGREE_LOG,
        // We expect some machines (e.g. register memory) to use up to 4x the number
        // of rows as main. By setting the max degree of main to be smaller by a factor
        // of 4, we ensure that we don't run out of rows in those machines.
        1 << (*powdr_linker::MAX_DEGREE_LOG - 2),
        runtime.submachines_declare(),
        preamble,
        initial_memory
            .into_iter()
            .format_with(",\n", |line, f| f(&format_args!("\t\t{line}"))),
        program
            .into_iter()
            .format_with("\n", |line, f| f(&format_args!("\t\t{line}"))),
    )
}

fn preamble(field: KnownField, runtime: &Runtime, with_bootloader: bool) -> String {
    let bootloader_preamble_if_included = if with_bootloader {
        bootloader_preamble(field)
    } else {
        "".to_string()
    };

    for machine in [
        "binary",
        "shift",
        "bit2",
        "bit6",
        "bit7",
        "byte",
        "byte2",
        "byte_binary",
        "byte_shift",
        "byte_compare",
    ] {
        assert!(
            runtime.has_submachine(machine),
            "RISC-V machine requires the `{machine}` submachine"
        );
    }

    let mul_instruction = mul_instruction(field, runtime);

    r#"
    reg pc[@pc];
    reg X[<=];
    reg Y[<=];
    reg Z[<=];
    reg W[<=];
"#
        .to_string()
        // runtime extra registers
        + &runtime
            .submachines_extra_registers()
            .into_iter()
            .map(|s| format!("\t\t{s}\n"))
            .join("")
        + &bootloader_preamble_if_included
        + &memory(with_bootloader)
        + r#"
    // =============== Register memory =======================
"# + "std::machines::large_field::memory::Memory regs(byte2);"
        + r#"
    // Get the value in register Y.
    instr get_reg Y -> X link ~> X = regs.mload(Y, STEP);

    // Set the value in register X to the value in register Y.
    instr set_reg X, Y -> link ~> regs.mstore(X, STEP, Y);

    // We still need these registers prover inputs.
    reg query_arg_1;
    reg query_arg_2;

    // Witness columns used in instuctions for intermediate values inside instructions.
    col witness tmp1_col;
    col witness tmp2_col;
    col witness tmp3_col;
    col witness tmp4_col;

    // We need to add these inline instead of using std::utils::is_zero
    // because when XX is not constrained, witgen will try to set XX,
    // XX_inv and XXIsZero to zero, which fails this constraint.
    // Therefore, we have to activate constrained whenever XXIsZero is used.
    // XXIsZero = 1 - XX * XX_inv
    col witness XX, XX_inv, XXIsZero;
    std::utils::force_bool(XXIsZero);
    XXIsZero * XX = 0;

    // ============== control-flow instructions ==============

    // Load the value of label `l` into register X.
    instr load_label X, l: label
        link ~> regs.mstore(X, STEP, tmp1_col)
    {
        tmp1_col = l
    }

    // Jump to `l` and store the return program counter in register W.
    instr jump l: label, W
        link ~> regs.mstore(W, STEP, pc + 1)
    {
        pc' = l
    }
    
    // Jump to the address in register X and store the return program counter in register W.
    instr jump_dyn X, W
        link ~> pc' = regs.mload(X, STEP)
        link ~> regs.mstore(W, STEP, pc + 1);

    // Jump to `l` if val(X) - val(Y) is nonzero, where X and Y are register ids.
    instr branch_if_diff_nonzero X, Y, l: label
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
    {
        XXIsZero = 1 - XX * XX_inv,
        XX = tmp1_col - tmp2_col,
        pc' = (1 - XXIsZero) * l + XXIsZero * (pc + 1)
    }

    // Jump to `l` if (val(X) - val(Y)) == Z, where X and Y are register ids and Z is a number.
    instr branch_if_diff_equal X, Y, Z, l: label
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
    {
        XXIsZero = 1 - XX * XX_inv,
        XX = tmp1_col - tmp2_col - Z,
        pc' = XXIsZero * l + (1 - XXIsZero) * (pc + 1)
    }

    // Skips W instructions if val(X) - val(Y) + Z is zero, where X and Y are register ids and Z is a
    // constant offset.
    instr skip_if_equal X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
    {
        XXIsZero = 1 - XX * XX_inv,
        XX = tmp1_col - tmp2_col + Z,
        pc' = pc + 1 + (XXIsZero * W)
    }

    // Branches to `l` if V = val(X) - val(Y) - Z is positive, i.e. val(X) - val(Y) > Z,
    // where X and Y are register ids and Z is a constant.
    // V is required to be the difference of two 32-bit unsigned values.
    // i.e. -2**32 < V < 2**32.
    instr branch_if_diff_greater_than X, Y, Z, l: label
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
    {
        (tmp1_col - tmp2_col - Z) + 2**32 - 1 = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000 + wrap_bit * 2**32,
        pc' = wrap_bit * l + (1 - wrap_bit) * (pc + 1)
    }

    // Stores 1 in register W if V = val(X) - val(Y) - Z is positive,
    // i.e. val(X) - val(Y) > Z, where X and Y are register ids and Z is a constant.
    // V is required to be the difference of two 32-bit unsigend values.
    // i.e. -2**32 < V < 2**32
    instr is_diff_greater_than X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> regs.mstore(W, STEP + 2, wrap_bit)
    {
        (tmp1_col - tmp2_col - Z) + 2**32 - 1 = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000 + wrap_bit * 2**32
    }

    // Stores val(X) * Z + W in register Y.
    instr affine X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> regs.mstore(Y, STEP + 1, tmp1_col * Z + W);

    // ================= wrapping instructions =================

    // Computes V = val(X) + val(Y) + Z, wraps it in 32 bits, and stores the result in register W.
    // Requires 0 <= V < 2**33.
    instr add_wrap X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> regs.mstore(W, STEP + 2, tmp3_col)
    {
        tmp1_col + tmp2_col + Z = tmp3_col + wrap_bit * 2**32,
        tmp3_col = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000
    }

    // Computes V = val(X) - val(Y) + Z, wraps it in 32 bits, and stores the result in register W.
    // Requires -2**32 <= V < 2**32.
    instr sub_wrap_with_offset X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> regs.mstore(W, STEP + 2, tmp3_col)
    {
        (tmp1_col - tmp2_col + Z) + 2**32 = tmp3_col + wrap_bit * 2**32,
        tmp3_col = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000
    }

    // ================= logical instructions =================

    // Stores 1 in register W if the value in register X is zero,
    // otherwise stores 0.
    instr is_equal_zero X, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> regs.mstore(W, STEP + 2, XXIsZero)
    {
        XXIsZero = 1 - XX * XX_inv,
        XX = tmp1_col
    }

    // Stores 1 in register W if val(X) == val(Y), otherwise stores 0.
    instr is_not_equal X, Y, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> regs.mstore(W, STEP + 2, tmp3_col)
    {
        XXIsZero = 1 - XX * XX_inv,
        XX = tmp1_col - tmp2_col,
        tmp3_col = 1 - XXIsZero
    }

    // ================= submachine instructions =================
"# + &runtime
        .submachines_instructions()
        .into_iter()
        .map(|s| format!("    {s}"))
        .join("\n")
        + r#"
    col witness X_b1;
    col witness X_b2;
    col witness X_b3;
    col witness X_b4;
    link => byte.check(X_b1);
    link => byte.check(X_b2);
    link => byte.check(X_b3);
    link => byte.check(X_b4);
    col witness wrap_bit;
    wrap_bit * (1 - wrap_bit) = 0;

    // Sign extends the value in register X and stores it in register Y.
    // Input is a 32 bit unsigned number. We check bit 7 and set all higher bits to that value.
    instr sign_extend_byte X, Y
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> regs.mstore(Y, STEP + 3, tmp3_col)
    {
        // wrap_bit is used as sign_bit here.
        tmp1_col = Y_7bit + wrap_bit * 0x80 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000,
        tmp3_col = Y_7bit + wrap_bit * 0xffffff80
    }
    col witness Y_7bit;
    link => bit7.check(Y_7bit);

    // Sign extends the value in register X and stores it in register Y.
    // Input is a 32 bit unsigned number. We check bit 15 and set all higher bits to that value.
    instr sign_extend_16_bits X, Y
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> regs.mstore(Y, STEP + 3, tmp3_col)
    {
        Y_15bit = X_b1 + Y_7bit * 0x100,

        // wrap_bit is used as sign_bit here.
        tmp1_col = Y_15bit + wrap_bit * 0x8000 + X_b3 * 0x10000 + X_b4 * 0x1000000,
        tmp3_col = Y_15bit + wrap_bit * 0xffff8000
    }
    col witness Y_15bit;

    // Converts the value in register X to a signed number and stores it in register Y.
    // Input is a 32 bit unsigned number (0 <= val(X) < 2**32) interpreted as a two's complement numbers.
    // Returns a signed number (-2**31 <= val(Y) < 2**31).
    instr to_signed X, Y
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> regs.mstore(Y, STEP + 1, tmp3_col)
    {
        // wrap_bit is used as sign_bit here.
        tmp1_col = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + Y_7bit * 0x1000000 + wrap_bit * 0x80000000,
        tmp3_col = tmp1_col - wrap_bit * 0x100000000
    }

    // ======================= assertions =========================

    instr fail { 1 = 0 }

    // Wraps V = val(X) * Y and stores it in register Z,
    // where X is a register and Y is a constant factor.
    // Removes up to 16 bits beyond 32
    // TODO is this really safe?
    instr wrap16 X, Y, Z
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> regs.mstore(Z, STEP + 3, tmp3_col)
    {
        (tmp1_col * Y) = Y_b5 * 2**32 + Y_b6 * 2**40 + tmp3_col,
        tmp3_col = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000
    }

    col witness Y_b5;
    col witness Y_b6;
    col witness Y_b7;
    col witness Y_b8;
    link => byte.check(Y_b5);
    link => byte.check(Y_b6);
    link => byte.check(Y_b7);
    link => byte.check(Y_b8);

    col witness REM_b1;
    col witness REM_b2;
    col witness REM_b3;
    col witness REM_b4;
    link => byte.check(REM_b1);
    link => byte.check(REM_b2);
    link => byte.check(REM_b3);
    link => byte.check(REM_b4);

    // Computes Q = val(Y) / val(X) and R = val(Y) % val(X) and stores them in registers Z and W.
    instr divremu Y, X, Z, W
        link ~> tmp1_col = regs.mload(Y, STEP)
        link ~> tmp2_col = regs.mload(X, STEP + 1)
        link ~> regs.mstore(Z, STEP + 2, tmp3_col)
        link ~> regs.mstore(W, STEP + 3, tmp4_col)
    {
        XXIsZero = 1 - XX * XX_inv,
        XX = tmp2_col,

        // if X is zero, remainder is set to dividend, as per RISC-V specification:
        tmp2_col * tmp3_col + tmp4_col = tmp1_col,

        // remainder >= 0:
        tmp4_col = REM_b1 + REM_b2 * 0x100 + REM_b3 * 0x10000 + REM_b4 * 0x1000000,

        // remainder < divisor, conditioned to val(X) not being 0:
        (1 - XXIsZero) * (tmp2_col - tmp4_col - 1 - Y_b5 - Y_b6 * 0x100 - Y_b7 * 0x10000 - Y_b8 * 0x1000000) = 0,

        // in case X is zero, we set quotient according to RISC-V specification
        XXIsZero * (tmp3_col - 0xffffffff) = 0,

        // quotient is 32 bits:
        tmp3_col = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000
    }
"# + mul_instruction
}

fn mul_instruction(field: KnownField, runtime: &Runtime) -> &'static str {
    match field {
        KnownField::Bn254Field => {
            // The BN254 field can fit any 64-bit number, so we can naively de-compose
            // Z * W into 8 bytes and put them together to get the upper and lower word.
            r#"
    // Computes V = val(X) * val(Y) and
    // stores the lower 32 bits in register Z and the upper 32 bits in register W.
    instr mul X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> regs.mstore(Z, STEP + 2, tmp3_col)
        link ~> regs.mstore(W, STEP + 3, tmp4_col)
    {
        tmp1_col * tmp2_col = tmp3_col + tmp4_col * 2**32,
        tmp3_col = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000,
        tmp4_col = Y_b5 + Y_b6 * 0x100 + Y_b7 * 0x10000 + Y_b8 * 0x1000000
    }
"#
        }
        KnownField::GoldilocksField => {
            assert!(
                runtime.has_submachine("split_gl"),
                "RISC-V machine with the goldilocks field requires the `split_gl` submachine"
            );
            // The Goldilocks field cannot fit some 64-bit numbers, so we have to use
            // the split machine. Note that it can fit a product of two 32-bit numbers.
            r#"
    // Computes V = val(X) * val(Y) and
    // stores the lower 32 bits in register Z and the upper 32 bits in register W.
    instr mul X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> (tmp3_col, tmp4_col) = split_gl.split(tmp1_col * tmp2_col)
        link ~> regs.mstore(Z, STEP + 2, tmp3_col)
        link ~> regs.mstore(W, STEP + 3, tmp4_col);
"#
        }
        KnownField::BabyBearField | KnownField::KoalaBearField | KnownField::Mersenne31Field => {
            panic!()
        }
    }
}

fn memory(with_bootloader: bool) -> String {
    let memory_machine = if with_bootloader {
        r#"
    std::machines::large_field::memory_with_bootloader_write::MemoryWithBootloaderWrite memory(byte2);

    // Stores val(W) at address (V = val(X) - val(Z) + Y) % 2**32.
    // V can be between 0 and 2**33.
    instr mstore_bootloader X, Z, Y, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Z, STEP + 1)
        link ~> tmp3_col = regs.mload(W, STEP + 2)
        link ~> memory.mstore_bootloader(X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000, STEP + 3, tmp3_col)
    {
        tmp1_col - tmp2_col + Y = (X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000) + wrap_bit * 2**32
    }
"#
    } else {
        r#"
    std::machines::large_field::memory::Memory memory(byte2);
"#
    };

    memory_machine.to_string()
        + r#"

    // Increased by 4 in each step, because we do up to 4 register memory accesses per step
    col fixed STEP(i) { 4 * i };

    // ============== memory instructions ==============

    /// Loads one word from an address V = val(X) + Y, where V can be between 0 and 2**33 (sic!),
    /// wraps the address to 32 bits and rounds it down to the next multiple of 4.
    /// Writes the loaded word and the remainder of the division by 4 to registers Z and W,
    /// respectively.
    instr mload X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp3_col = memory.mload(X_b4 * 0x1000000 + X_b3 * 0x10000 + X_b2 * 0x100 + X_b1 * 4, STEP + 1)
        link ~> regs.mstore(Z, STEP + 2, tmp3_col)
        link ~> regs.mstore(W, STEP + 3, tmp4_col)
        link => bit2.check(tmp4_col)
        link => bit6.check(X_b1)
    {
        tmp1_col + Y = wrap_bit * 2**32 + X_b4 * 0x1000000 + X_b3 * 0x10000 + X_b2 * 0x100 + X_b1 * 4 + tmp4_col
    }

    // Stores val(W) at address (V = val(X) - val(Y) + Z) % 2**32.
    // V can be between 0 and 2**33.
    // V should be a multiple of 4, but this instruction does not enforce it.
    instr mstore X, Y, Z, W
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> tmp3_col = regs.mload(W, STEP + 2)
        link ~> memory.mstore(X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000, STEP + 3, tmp3_col)
    {
        tmp1_col - tmp2_col + Z = (X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000) + wrap_bit * 2**32
    }
"#
}

fn only_if_no_write_to_zero(reg: Register, statement: String) -> Vec<String> {
    only_if_no_write_to_zero_vec(reg, vec![statement])
}

fn only_if_no_write_to_zero_vec(reg: Register, statements: Vec<String>) -> Vec<String> {
    if reg.is_zero() {
        vec![]
    } else {
        statements
    }
}

/// Push register into the stack

pub fn push_register(name: &str) -> Vec<String> {
    assert!(name.starts_with('x'), "Only x registers are supported");
    let reg = Register::from(name);
    vec![
        // x2 + x0 - 4 => x2
        format!("add_wrap 2, 0, -4, 2;",),
        format!("mstore 2, 0, 0, {};", reg.addr()),
    ]
}

/// Pop register from the stack
pub fn pop_register(name: &str) -> Vec<String> {
    assert!(name.starts_with('x'), "Only x registers are supported");
    let reg = Register::from(name);
    vec![
        format!(
            "mload 2, 0, {}, {};",
            reg.addr(),
            Register::from("tmp1").addr()
        ),
        "add_wrap 2, 0, 4, 2;".to_string(),
    ]
}

fn process_instruction<A: InstructionArgs>(instr: &str, args: A) -> Result<Vec<String>, A::Error> {
    let tmp1 = Register::from("tmp1");
    let tmp2 = Register::from("tmp2");
    let tmp3 = Register::from("tmp3");
    let tmp4 = Register::from("tmp4");
    let lr_sc_reservation = Register::from("lr_sc_reservation");
    let statements = match instr {
        // load/store registers
        "li" | "la" => {
            // The difference between "li" and "la" in RISC-V is that the former
            // is for loading values as is, and the later is for loading PC
            // relative values. But since we work on a higher abstraction level,
            // for us they are the same thing.
            if let Ok((rd, label)) = args.rl() {
                let label = escape_label(label.as_ref());
                only_if_no_write_to_zero(rd, format!("load_label {}, {label};", rd.addr()))
            } else {
                let (rd, imm) = args.ri()?;
                only_if_no_write_to_zero(rd, format!("set_reg {}, {imm};", rd.addr()))
            }
        }
        // TODO check if it is OK to clear the lower order bits
        "lui" => {
            let (rd, imm) = args.ri()?;
            only_if_no_write_to_zero(rd, format!("set_reg {}, {};", rd.addr(), imm << 12))
        }
        "mv" => {
            let (rd, rs) = args.rr()?;
            only_if_no_write_to_zero(rd, format!("affine {}, {}, 1, 0;", rs.addr(), rd.addr()))
        }

        // Arithmetic
        "add" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "add_wrap {}, {}, {}, {};",
                    r1.addr(),
                    r2.addr(),
                    0,
                    rd.addr()
                ),
            )
        }
        "addi" => {
            let (rd, rs, imm) = args.rri()?;
            only_if_no_write_to_zero(
                rd,
                format!("add_wrap {}, 0, {imm}, {};", rs.addr(), rd.addr()),
            )
        }
        "sub" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "sub_wrap_with_offset {}, {}, 0, {};",
                    r1.addr(),
                    r2.addr(),
                    rd.addr()
                ),
            )
        }
        "neg" => {
            let (rd, r1) = args.rr()?;
            only_if_no_write_to_zero(
                rd,
                format!("sub_wrap_with_offset 0, {}, 0, {};", r1.addr(), rd.addr()),
            )
        }
        "mul" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "mul {}, {}, {}, {};",
                    r1.addr(),
                    r2.addr(),
                    rd.addr(),
                    tmp1.addr()
                ),
            )
        }
        "mulhu" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "mul {}, {}, {}, {};",
                    r1.addr(),
                    r2.addr(),
                    tmp1.addr(),
                    rd.addr(),
                ),
            )
        }
        "mulh" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                    format!("to_signed {}, {};", r2.addr(), tmp2.addr()),
                    // tmp3 is 1 if tmp1 is non-negative
                    format!(
                        "is_diff_greater_than {}, 0, -1, {};",
                        tmp1.addr(),
                        tmp3.addr()
                    ),
                    // tmp4 is 1 if tmp2 is non-negative
                    format!(
                        "is_diff_greater_than {}, 0, -1, {};",
                        tmp2.addr(),
                        tmp4.addr()
                    ),
                    // If tmp1 is negative, convert to positive
                    format!("skip_if_equal 0, {}, 1, 1;", tmp3.addr()),
                    format!("affine {}, {}, -1, 0;", tmp1.addr(), tmp1.addr()),
                    // If tmp2 is negative, convert to positive
                    format!("skip_if_equal 0, {}, 1, 1;", tmp4.addr()),
                    format!("affine {}, {}, -1, 0;", tmp2.addr(), tmp2.addr()),
                    format!(
                        "mul {}, {}, {}, {};",
                        tmp1.addr(),
                        tmp2.addr(),
                        tmp1.addr(),
                        rd.addr()
                    ),
                    // Determine the sign of the result based on the signs of tmp1 and tmp2
                    format!(
                        "is_not_equal {}, {}, {};",
                        tmp3.addr(),
                        tmp4.addr(),
                        tmp3.addr()
                    ),
                    // If the result should be negative, convert back to negative
                    format!("skip_if_equal {}, 0, 0, 2;", tmp3.addr()),
                    format!("is_equal_zero {}, {};", tmp1.addr(), tmp1.addr()),
                    format!(
                        "sub_wrap_with_offset {}, {}, -1, {};",
                        tmp1.addr(),
                        rd.addr(),
                        rd.addr()
                    ),
                ],
            )
        }
        "mulhsu" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                    // tmp2 is 1 if tmp1 is non-negative
                    format!(
                        "is_diff_greater_than {}, 0, -1, {};",
                        tmp1.addr(),
                        tmp2.addr()
                    ),
                    // If negative, convert to positive
                    format!("skip_if_equal 0, {}, 1, 1;", tmp2.addr()),
                    format!("affine {}, {}, -1, 0;", tmp1.addr(), tmp1.addr()),
                    format!(
                        "mul {}, {}, {}, {};",
                        tmp1.addr(),
                        r2.addr(),
                        tmp1.addr(),
                        rd.addr()
                    ),
                    // If was negative before, convert back to negative
                    format!("skip_if_equal 0, {}, 1, 2;", tmp2.addr()),
                    format!("is_equal_zero {}, {};", tmp1.addr(), tmp1.addr()),
                    // If the lower bits are zero, return the two's complement,
                    // otherwise return one's complement.
                    format!(
                        "sub_wrap_with_offset {}, {}, -1, {};",
                        tmp1.addr(),
                        rd.addr(),
                        rd.addr()
                    ),
                ],
            )
        }
        "divu" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "divremu {}, {}, {}, {};",
                    r1.addr(),
                    r2.addr(),
                    rd.addr(),
                    tmp1.addr()
                ),
            )
        }
        "remu" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "divremu {}, {}, {}, {};",
                    r1.addr(),
                    r2.addr(),
                    tmp1.addr(),
                    rd.addr()
                ),
            )
        }

        // bitwise
        "xor" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!("xor {}, {}, 0, {};", r1.addr(), r2.addr(), rd.addr()),
            )
        }
        "xori" => {
            let (rd, r1, imm) = args.rri()?;
            only_if_no_write_to_zero(rd, format!("xor {}, 0, {imm}, {};", r1.addr(), rd.addr()))
        }
        "and" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!("and {}, {}, 0, {};", r1.addr(), r2.addr(), rd.addr()),
            )
        }
        "andi" => {
            let (rd, r1, imm) = args.rri()?;
            only_if_no_write_to_zero(rd, format!("and {}, 0, {imm}, {};", r1.addr(), rd.addr()))
        }
        "or" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!("or {}, {}, 0, {};", r1.addr(), r2.addr(), rd.addr()),
            )
        }
        "ori" => {
            let (rd, r1, imm) = args.rri()?;
            only_if_no_write_to_zero(rd, format!("or {}, 0, {imm}, {};", r1.addr(), rd.addr()))
        }
        "not" => {
            let (rd, rs) = args.rr()?;
            only_if_no_write_to_zero(
                rd,
                format!("sub_wrap_with_offset 0, {}, -1, {};", rs.addr(), rd.addr()),
            )
        }

        // shift
        "slli" => {
            let (rd, rs, amount) = args.rri()?;
            assert!(amount <= 31);
            only_if_no_write_to_zero_vec(
                rd,
                if amount <= 16 {
                    vec![format!(
                        "wrap16 {}, {}, {};",
                        rs.addr(),
                        1 << amount,
                        rd.addr()
                    )]
                } else {
                    vec![
                        format!("wrap16 {}, {}, {};", rs.addr(), 1 << 16, tmp1.addr()),
                        format!(
                            "wrap16 {}, {}, {};",
                            tmp1.addr(),
                            1 << (amount - 16),
                            rd.addr()
                        ),
                    ]
                },
            )
        }
        "sll" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("and {}, 0, 0x1f, {};", r2.addr(), tmp1.addr()),
                    format!("shl {}, {}, 0, {};", r1.addr(), tmp1.addr(), rd.addr()),
                ],
            )
        }
        "srli" => {
            // logical shift right
            let (rd, rs, amount) = args.rri()?;
            assert!(amount <= 31);
            only_if_no_write_to_zero(
                rd,
                format!("shr {}, 0, {amount}, {};", rs.addr(), rd.addr()),
            )
        }
        "srl" => {
            // logical shift right
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("and {}, 0, 0x1f, {};", r2.addr(), tmp1.addr()),
                    format!("shr {}, {}, 0, {};", r1.addr(), tmp1.addr(), rd.addr()),
                ],
            )
        }
        "srai" => {
            // arithmetic shift right
            // TODO see if we can implement this directly with a machine.
            // Now we are using the equivalence
            // a >>> b = (a >= 0 ? a >> b : ~(~a >> b))
            let (rd, rs, amount) = args.rri()?;
            assert!(amount <= 31);
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("to_signed {}, {};", rs.addr(), tmp1.addr()),
                    format!(
                        "is_diff_greater_than 0, {}, 0, {};",
                        tmp1.addr(),
                        tmp1.addr()
                    ),
                    format!("affine {}, {}, 0xffffffff, 0;", tmp1.addr(), tmp1.addr()),
                    // Here, tmp1 is the full bit mask if rs is negative
                    // and zero otherwise.
                    format!("xor {}, {}, 0, {};", tmp1.addr(), rs.addr(), rd.addr()),
                    format!("shr {}, 0, {amount}, {};", rd.addr(), rd.addr()),
                    format!("xor {}, {}, 0, {};", tmp1.addr(), rd.addr(), rd.addr()),
                ],
            )
        }

        // comparison
        "seqz" => {
            let (rd, rs) = args.rr()?;
            only_if_no_write_to_zero(rd, format!("is_equal_zero {}, {};", rs.addr(), rd.addr()))
        }
        "snez" => {
            let (rd, rs) = args.rr()?;
            only_if_no_write_to_zero(rd, format!("is_not_equal {}, 0, {};", rs.addr(), rd.addr()))
        }
        "slti" => {
            let (rd, rs, imm) = args.rri()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("to_signed {}, {};", rs.addr(), tmp1.addr()),
                    format!(
                        "is_diff_greater_than 0, {}, -({}), {};",
                        tmp1.addr(),
                        imm as i32,
                        rd.addr()
                    ),
                ],
            )
        }
        "slt" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                    format!("to_signed {}, {};", r2.addr(), tmp2.addr()),
                    format!(
                        "is_diff_greater_than {}, {}, 0, {};",
                        tmp2.addr(),
                        tmp1.addr(),
                        rd.addr()
                    ),
                ],
            )
        }
        "sltiu" => {
            let (rd, rs, imm) = args.rri()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "is_diff_greater_than 0, {}, -({imm}), {};",
                    rs.addr(),
                    rd.addr()
                ),
            )
        }
        "sltu" => {
            let (rd, r1, r2) = args.rrr()?;
            only_if_no_write_to_zero(
                rd,
                format!(
                    "is_diff_greater_than {}, {}, 0, {};",
                    r2.addr(),
                    r1.addr(),
                    rd.addr()
                ),
            )
        }
        "sgtz" => {
            let (rd, rs) = args.rr()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!("to_signed {}, {};", rs.addr(), tmp1.addr()),
                    format!("is_diff_greater_than {}, 0, 0, {};", tmp1.addr(), rd.addr()),
                ],
            )
        }

        // branching
        "beq" => {
            let (r1, r2, label) = args.rrl()?;
            let label = escape_label(label.as_ref());
            vec![format!(
                "branch_if_diff_equal {}, {}, 0, {label};",
                r1.addr(),
                r2.addr()
            )]
        }
        "beqz" => {
            let (r1, label) = args.rl()?;
            let label = escape_label(label.as_ref());
            vec![format!(
                "branch_if_diff_equal {}, 0, 0, {label};",
                r1.addr()
            )]
        }
        "bgeu" => {
            let (r1, r2, label) = args.rrl()?;
            let label = escape_label(label.as_ref());
            // TODO does this fulfill the input requirements for branch_if_diff_greater_than?
            vec![format!(
                "branch_if_diff_greater_than {}, {}, -1, {label};",
                r1.addr(),
                r2.addr()
            )]
        }
        "bgez" => {
            let (r1, label) = args.rl()?;
            let label = escape_label(label.as_ref());
            vec![
                format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                format!(
                    "branch_if_diff_greater_than {}, 0, -1, {label};",
                    tmp1.addr()
                ),
            ]
        }
        "bltu" => {
            let (r1, r2, label) = args.rrl()?;
            let label = escape_label(label.as_ref());
            vec![format!(
                "branch_if_diff_greater_than {}, {}, 0, {label};",
                r2.addr(),
                r1.addr()
            )]
        }
        "blt" => {
            let (r1, r2, label) = args.rrl()?;
            let label = escape_label(label.as_ref());
            // Branch if r1 < r2 (signed).
            // TODO does this fulfill the input requirements for branch_if_diff_greater_than?
            vec![
                format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                format!("to_signed {}, {};", r2.addr(), tmp2.addr()),
                format!(
                    "branch_if_diff_greater_than {}, {}, 0, {label};",
                    tmp2.addr(),
                    tmp1.addr()
                ),
            ]
        }
        "bge" => {
            let (r1, r2, label) = args.rrl()?;
            let label = escape_label(label.as_ref());
            // Branch if r1 >= r2 (signed).
            // TODO does this fulfill the input requirements for branch_if_diff_greater_than?
            vec![
                format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                format!("to_signed {}, {};", r2.addr(), tmp2.addr()),
                format!(
                    "branch_if_diff_greater_than {}, {}, -1, {label};",
                    tmp1.addr(),
                    tmp2.addr()
                ),
            ]
        }
        "bltz" => {
            // branch if 2**31 <= r1 < 2**32
            let (r1, label) = args.rl()?;
            let label = escape_label(label.as_ref());
            vec![format!(
                "branch_if_diff_greater_than {}, 0, 2**31 - 1, {label};",
                r1.addr()
            )]
        }
        "blez" => {
            // branch less or equal zero
            let (r1, label) = args.rl()?;
            let label = escape_label(label.as_ref());
            vec![
                format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                format!(
                    "branch_if_diff_greater_than 0, {}, -1, {label};",
                    tmp1.addr()
                ),
            ]
        }
        "bgtz" => {
            // branch if 0 < r1 < 2**31
            let (r1, label) = args.rl()?;
            let label = escape_label(label.as_ref());
            vec![
                format!("to_signed {}, {};", r1.addr(), tmp1.addr()),
                format!(
                    "branch_if_diff_greater_than {}, 0, 0, {label};",
                    tmp1.addr()
                ),
            ]
        }
        "bne" => {
            let (r1, r2, label) = args.rrl()?;
            let label = escape_label(label.as_ref());
            vec![format!(
                "branch_if_diff_nonzero {}, {}, {label};",
                r1.addr(),
                r2.addr()
            )]
        }
        "bnez" => {
            let (r1, label) = args.rl()?;
            let label = escape_label(label.as_ref());
            vec![format!("branch_if_diff_nonzero {}, 0, {label};", r1.addr())]
        }

        // jump and call
        "j" | "tail" => {
            let label = args.l()?;
            let label = escape_label(label.as_ref());
            vec![format!("jump {label}, {};", tmp1.addr(),)]
        }
        "jr" => {
            let rs = args.r()?;
            vec![format!("jump_dyn {}, {};", rs.addr(), tmp1.addr())]
        }
        "jal" => {
            if let Ok(label) = args.l() {
                let label = escape_label(label.as_ref());
                vec![format!("jump {label}, 1;")]
            } else {
                let (rd, label) = args.rl()?;
                let label = escape_label(label.as_ref());
                if rd.is_zero() {
                    vec![format!("jump {label}, {};", tmp1.addr())]
                } else {
                    vec![format!("jump {label}, {};", rd.addr())]
                }
            }
        }
        "jalr" => {
            if let Ok(rs) = args.r() {
                vec![format!("jump_dyn {}, 1;", rs.addr())]
            } else {
                let (rd, rs, off) = args.rro()?;
                assert_eq!(off, 0, "jalr with non-zero offset is not supported");
                if rd.is_zero() {
                    vec![format!("jump_dyn {}, {};", rs.addr(), tmp1.addr())]
                } else {
                    vec![format!("jump_dyn {}, {};", rs.addr(), rd.addr())]
                }
            }
        }
        "call" => {
            let label = args.l()?;
            let label = escape_label(label.as_ref());
            vec![format!("jump {label}, 1;")]
        }
        "ecall" => {
            args.empty()?;
            // save ra/x1
            push_register("x1")
                .into_iter()
                // jump to to handler
                .chain(["jump __ecall_handler, 1;".to_string()])
                // restore ra/x1
                .chain(pop_register("x1"))
                .collect()
        }
        "ebreak" => {
            args.empty()?;
            // we don't use ebreak for anything, ignore
            vec![]
        }
        "ret" => {
            args.empty()?;
            vec![format!("jump_dyn 1, {};", tmp1.addr())]
        }

        // memory access
        "lw" => {
            let (rd, rs, off) = args.rro()?;
            // TODO we need to consider misaligned loads / stores
            only_if_no_write_to_zero(
                rd,
                format!(
                    "mload {}, {off}, {}, {};",
                    rs.addr(),
                    rd.addr(),
                    tmp1.addr()
                ),
            )
        }
        "lb" => {
            // load byte and sign-extend. the memory is little-endian.
            let (rd, rs, off) = args.rro()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!(
                        "mload {}, {off}, {}, {};",
                        rs.addr(),
                        tmp1.addr(),
                        tmp2.addr()
                    ),
                    format!("affine {}, {}, 8, 0;", tmp2.addr(), tmp2.addr()),
                    format!("shr {}, {}, 0, {};", tmp1.addr(), tmp2.addr(), tmp1.addr()),
                    format!("sign_extend_byte {}, {};", tmp1.addr(), rd.addr()),
                ],
            )
        }
        "lbu" => {
            // load byte and zero-extend. the memory is little-endian.
            let (rd, rs, off) = args.rro()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!(
                        "mload {}, {off}, {}, {};",
                        rs.addr(),
                        tmp1.addr(),
                        tmp2.addr()
                    ),
                    format!("affine {}, {}, 8, 0;", tmp2.addr(), tmp2.addr()),
                    format!("shr {}, {}, 0, {};", tmp1.addr(), tmp2.addr(), tmp1.addr()),
                    format!("and {}, 0, 0xff, {};", tmp1.addr(), rd.addr()),
                ],
            )
        }
        "lh" => {
            // Load two bytes and sign-extend.
            // Assumes the address is a multiple of two.
            let (rd, rs, off) = args.rro()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!(
                        "mload {}, {off}, {}, {};",
                        rs.addr(),
                        tmp1.addr(),
                        tmp2.addr()
                    ),
                    format!("affine {}, {}, 8, 0;", tmp2.addr(), tmp2.addr()),
                    format!("shr {}, {}, 0, {};", tmp1.addr(), tmp2.addr(), tmp1.addr()),
                    format!("sign_extend_16_bits {}, {};", tmp1.addr(), rd.addr()),
                ],
            )
        }
        "lhu" => {
            // Load two bytes and zero-extend.
            // Assumes the address is a multiple of two.
            let (rd, rs, off) = args.rro()?;
            only_if_no_write_to_zero_vec(
                rd,
                vec![
                    format!(
                        "mload {}, {off}, {}, {};",
                        rs.addr(),
                        tmp1.addr(),
                        tmp2.addr()
                    ),
                    format!("affine {}, {}, 8, 0;", tmp2.addr(), tmp2.addr()),
                    format!("shr {}, {}, 0, {};", tmp1.addr(), tmp2.addr(), tmp1.addr()),
                    format!("and {}, 0, 0x0000ffff, {};", tmp1.addr(), rd.addr()),
                ],
            )
        }
        "sw" => {
            let (r2, r1, off) = args.rro()?;
            vec![format!("mstore {}, 0, {off}, {};", r1.addr(), r2.addr())]
        }
        "sh" => {
            // store half word (two bytes)
            // TODO this code assumes it is at least aligned on
            // a two-byte boundary

            let (r2, r1, off) = args.rro()?;
            vec![
                format!(
                    "mload {}, {off}, {}, {};",
                    r1.addr(),
                    tmp1.addr(),
                    tmp2.addr()
                ),
                format!("set_reg {}, 0xffff;", tmp3.addr()),
                format!("affine {}, {}, 8, 0;", tmp2.addr(), tmp4.addr()),
                format!("shl {}, {}, 0, {};", tmp3.addr(), tmp4.addr(), tmp3.addr()),
                format!("xor {}, 0, 0xffffffff, {};", tmp3.addr(), tmp3.addr()),
                format!("and {}, {}, 0, {};", tmp1.addr(), tmp3.addr(), tmp1.addr()),
                format!("and {}, 0, 0xffff, {};", r2.addr(), tmp3.addr()),
                format!("shl {}, {}, 0, {};", tmp3.addr(), tmp4.addr(), tmp3.addr()),
                format!("or {}, {}, 0, {};", tmp1.addr(), tmp3.addr(), tmp1.addr()),
                format!(
                    "mstore {}, {}, {off}, {};",
                    r1.addr(),
                    tmp2.addr(),
                    tmp1.addr()
                ),
            ]
        }
        "sb" => {
            // store byte
            let (r2, r1, off) = args.rro()?;
            vec![
                format!(
                    "mload {}, {off}, {}, {};",
                    r1.addr(),
                    tmp1.addr(),
                    tmp2.addr()
                ),
                format!("set_reg {}, 0xff;", tmp3.addr()),
                format!("affine {}, {}, 8, 0;", tmp2.addr(), tmp4.addr()),
                format!("shl {}, {}, 0, {};", tmp3.addr(), tmp4.addr(), tmp3.addr()),
                format!("xor {}, 0, 0xffffffff, {};", tmp3.addr(), tmp3.addr()),
                format!("and {}, {}, 0, {};", tmp1.addr(), tmp3.addr(), tmp1.addr()),
                format!("and {}, 0, 0xff, {};", r2.addr(), tmp3.addr()),
                format!("shl {}, {}, 0, {};", tmp3.addr(), tmp4.addr(), tmp3.addr()),
                format!("or {}, {}, 0, {};", tmp1.addr(), tmp3.addr(), tmp1.addr()),
                format!(
                    "mstore {}, {}, {off}, {};",
                    r1.addr(),
                    tmp2.addr(),
                    tmp1.addr()
                ),
            ]
        }
        "fence" | "nop" => vec![],
        "unimp" => vec!["fail;".to_string()],

        // atomic instructions
        insn if insn.starts_with("amoadd.w") => {
            let (rd, rs2, rs1) = args.rrr2()?;

            [
                vec![
                    format!("mload {}, 0, {}, {};", rs1.addr(), tmp1.addr(), tmp2.addr()),
                    format!(
                        "add_wrap {}, {}, 0, {};",
                        tmp1.addr(),
                        rs2.addr(),
                        tmp2.addr()
                    ),
                    format!("mstore {}, 0, 0, {};", rs1.addr(), tmp2.addr()),
                ],
                only_if_no_write_to_zero(
                    rd,
                    format!("affine {}, {}, 1, 0;", tmp1.addr(), rd.addr()),
                ),
            ]
            .concat()
        }

        insn if insn.starts_with("lr.w") => {
            // Very similar to "lw":
            let (rd, rs) = args.rr()?;
            // TODO misaligned access should raise misaligned address exceptions
            [
                only_if_no_write_to_zero_vec(
                    rd,
                    vec![format!(
                        "mload {}, 0, {}, {};",
                        rs.addr(),
                        rd.addr(),
                        tmp1.addr()
                    )],
                ),
                vec![format!("set_reg {}, 1;", lr_sc_reservation.addr())],
            ]
            .concat()
        }

        insn if insn.starts_with("sc.w") => {
            // Some overlap with "sw", but also writes 0 to rd on success
            let (rd, rs2, rs1) = args.rrr2()?;
            // TODO: misaligned access should raise misaligned address exceptions
            [
                format!("skip_if_equal {}, 0, 0, 1;", lr_sc_reservation.addr()),
                format!("mstore {}, 0, 0, {};", rs1.addr(), rs2.addr()),
            ]
            .into_iter()
            .chain(only_if_no_write_to_zero_vec(
                rd,
                vec![format!(
                    "affine {}, {}, -1, 1;",
                    lr_sc_reservation.addr(),
                    rd.addr()
                )],
            ))
            .chain([format!("set_reg {}, 0;", lr_sc_reservation.addr())])
            .collect()
        }

        _ => {
            panic!("Unknown instruction: {instr}");
        }
    };
    for s in &statements {
        log::debug!("          {s}");
    }
    Ok(statements)
}
