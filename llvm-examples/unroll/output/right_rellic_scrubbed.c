void right(unsigned int N);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_18989b541471998acea3ba6b5f4461ab[30] = "llvm-examples/unroll/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_008eee418d4229b5969b3d61ddac92ee = {"llvm-examples/unroll/right.rs", "\035\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_f5fb85dd27a38af5b5bac898394b9cbc = {"llvm-examples/unroll/right.rs", "\035\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};
void right(unsigned int N) {
    char N_var0[4];
    char i[4];
    char x[4];
    struct literal_struct_0 call3;
    struct literal_struct_0 call4;
    *(unsigned int *)(&N_var0) = N;
    *(unsigned int *)(&x) = 0U;
    *(unsigned int *)(&i) = 1U;
    if ((int)(*(unsigned int *)(&i)) > (int)N) {
    } else {
        call3 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&x), *(unsigned int *)(&i));
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)N && !call3.field1) {
        *(unsigned int *)(&x) = call3.field0;
        call4 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&i), 1U);
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)N && !call4.field1 && !call3.field1) {
        *(unsigned int *)(&i) = call4.field0;
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)N && !call3.field1 && call4.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_f5fb85dd27a38af5b5bac898394b9cbc);
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)N && call3.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_008eee418d4229b5969b3d61ddac92ee);
    }
}
