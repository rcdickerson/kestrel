void right(unsigned int n);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_72b76b03aa3be83f823e552e2267c704[28] = "llvm-examples/loop/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_cec36e1e6db6a74003dcc27714188173 = {"llvm-examples/loop/right.rs", "\033\000\000\000\000\000\000\000\005\000\000\000\017\000\000\000"};
struct literal_struct_1 alloc_83591e49dc36b934441419653b8254c2 = {"llvm-examples/loop/right.rs", "\033\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
void right(unsigned int n) {
    char n_var0[4];
    char i[4];
    char sum[4];
    struct literal_struct_0 call3;
    struct literal_struct_0 call4;
    *(unsigned int *)(&n_var0) = n;
    *(unsigned int *)(&sum) = 0U;
    *(unsigned int *)(&i) = 1U;
    if ((int)(*(unsigned int *)(&i)) > (int)n) {
        return;
    } else {
        call3 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&sum), *(unsigned int *)(&i));
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)n && !call3.field1) {
        *(unsigned int *)(&sum) = call3.field0;
        call4 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&i), 1U);
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)n && !call4.field1 && !call3.field1) {
        *(unsigned int *)(&i) = call4.field0;
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)n && !call3.field1 && call4.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_83591e49dc36b934441419653b8254c2);
    }
    if ((int)(*(unsigned int *)(&i)) <= (int)n && call3.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_cec36e1e6db6a74003dcc27714188173);
    }
}
