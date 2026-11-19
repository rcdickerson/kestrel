void right(unsigned int x);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_443ca199dae137e72c94c49604c0250d[30] = "llvm-examples/simple/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_b39206fbe48ecb1e8d276ee35c6d01f2 = {"llvm-examples/simple/right.rs", "\035\000\000\000\000\000\000\000\002\000\000\000\025\000\000\000"};
void right(unsigned int x) {
    char ret_val[4];
    char x_var1[4];
    struct literal_struct_0 call2;
    *(unsigned int *)(&x_var1) = x;
    call2 = llvm_sadd_with_overflow_i32(x, 1U);
    if (!call2.field1) {
        *(unsigned int *)(&ret_val) = call2.field0;
    } else {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_b39206fbe48ecb1e8d276ee35c6d01f2);
    }
}
