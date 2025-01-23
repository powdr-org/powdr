{{IMPORTS}}

let MIN_DEGREE_LOG: int = {{MIN_DEGREE_LOG}};
let MIN_DEGREE: int = 2**MIN_DEGREE_LOG;
let MAX_DEGREE_LOG: int = {{MAX_DEGREE_LOG}};
let MAIN_MAX_DEGREE: int = 2**MAX_DEGREE_LOG;
let LARGE_SUBMACHINES_MAX_DEGREE: int = 2**(MAX_DEGREE_LOG + 2);

machine Main with min_degree: MIN_DEGREE, max_degree: {{MAIN_MAX_DEGREE}} {

    reg pc[@pc];
    reg X[<=];
    reg Y[<=];
    reg Z[<=];
    reg W[<=];
    {{SUBMACHINE_EXTRA_REGISTERS}}

    // We still need these registers for prover inputs.
    reg query_arg_1;
    reg query_arg_2;

    std::machines::large_field::memory::Memory regs(byte2, MIN_DEGREE, LARGE_SUBMACHINES_MAX_DEGREE);
    {{MEMORY_DECLARATION}}
    {{SUBMACHINE_DECLARATIONS}}

    let initial_memory: (fe, fe)[] = [
        {{INITIAL_MEMORY}}
    ];

    // Initial and final memory addresses of prover data.
    // The data is to be filled in by the prover in this range.
    let prover_data_start: fe = {{PROVER_DATA_START}};
    let prover_data_end: fe = {{PROVER_DATA_END}};

    // ================= Extra columns we use to hold temporary values inside instructions.
    col witness tmp1_col;
    col witness tmp2_col;
    col witness tmp3_col;
    col witness tmp4_col;

    col witness X_b1;
    col witness X_b2;
    col witness X_b3;
    col witness X_b4;
    link => byte.check(X_b1);
    link => byte.check(X_b2);
    link => byte.check(X_b3);
    link => byte.check(X_b4);

    col witness Y_7bit;
    link => bit7.check(Y_7bit);
    col witness Y_15bit;

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

    // TODO std::utils::force_bool doesn't work with witgen at this level
    col witness wrap_bit;
    wrap_bit * (1 - wrap_bit) = 0;

    // We need to add these inline instead of using std::utils::is_zero
    // because when XX is not constrained, witgen will try to set XX,
    // XX_inv and XXIsZero to zero, which fails this constraint.
    // Therefore, we have to activate constrained whenever XXIsZero is used.
    // XXIsZero = 1 - XX * XX_inv
    col witness XX, XX_inv, XXIsZero;
    std::utils::force_bool(XXIsZero);
    XXIsZero * XX = 0;

    // =============== Register memory =======================
    // Get the value in register Y.
    instr get_reg Y -> X link ~> X = regs.mload(Y, STEP);

    // Set the value in register X to the value in register Y.
    instr set_reg X, Y -> link ~> regs.mstore(X, STEP, Y);

    // ================ Publics ==================
    std::machines::write_once_memory_with_8_publics::WriteOnceMemoryWith8Publics publics;
    instr commit_public X, Y link => publics.access(tmp1_col, tmp2_col)
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP);
    // ===========================================

    // Increased by 4 in each step, because we do up to 4 register memory accesses per step
    col fixed STEP(i) { 3000 * i };

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
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> regs.mstore(W, STEP, pc + 1)
    {
        // TODO: using a tmp col here avoids an extra selector column, because
        // links with next references on LHS can't currently be merged with other links
        pc' = tmp1_col
    }

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

    instr fail
        link ~> tmp1_col = regs.mload(0, STEP)
    {
        tmp1_col = 1
    }

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

    {{MUL_INSTRUCTION}}

    // ================= ground field arithmetic =================

    // Inverts a Goldilocks field value inplace.
    //
    // X and Y are low and high limbs of the field element to invert, respectively.
    //
    // Unsolvable if the value is 0.
    instr invert_gl X, Y
        link ~> tmp1_col = regs.mload(X, STEP)
        link ~> tmp2_col = regs.mload(Y, STEP + 1)
        link ~> (tmp3_col, tmp4_col) = split_gl.split(XX_inv)
        link ~> regs.mstore(X, STEP + 2, tmp3_col)
        link ~> regs.mstore(Y, STEP + 3, tmp4_col)
    {
        {{INVERT_GL_INSTRUCTION_BODY}}
    }
    // ================= submachine instructions =================
    {{SUBMACHINE_INSTRUCTIONS}}

    // ================= bootloader instructions =================
    {{BOOTLOADER_INSTRUCTIONS}}

    // ================= compiled program =================
    function main {
        {{PROGRAM}}
    }
}
