mod types {
    enum DoubleOpt<T> {
        None,
        Some(T, T)
    }

    struct MyStruct<T> {
        a: int,
        b: DoubleOpt<T>,
        c: T
    }
}


machine Empty with degree: 4 {
    col witness w;
    w = w * w;
}