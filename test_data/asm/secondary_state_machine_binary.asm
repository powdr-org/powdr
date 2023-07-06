reg pc[@pc];
reg X[<=];
reg Y[<=];
reg A;
reg B;


pil{
    // Decomposes a byte into 2 4-bit values, adds 1 to each of them (via a lookup), and puts it back together
    col fixed binary_RESET(i) { i % 2 };

    col fixed binary_P_A(i) { i % 16 };
    col fixed binary_P_B(i) {
        (binary_P_A(i) + 1) & 0xf
    };

    col witness binary_A_byte;
    col witness binary_B_byte;

    {binary_A_byte, binary_B_byte} in {binary_P_A, binary_P_B};

    col witness binary_A;
    col witness binary_B;

    binary_A' = 16 * binary_A * (1 - binary_RESET) + binary_A_byte;
    binary_B' = 16 * binary_B * (1 - binary_RESET) + binary_B_byte;

}


instr add_one_to_each_4bit Y -> X {
    {Y, X} in binary_RESET { binary_A, binary_B }
}
instr loop { pc' = pc }

// Set input
A <=X= 0x12;
B <=X= 0xff;

B <=X= add_one_to_each_4bit(A);

loop;