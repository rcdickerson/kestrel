void right(unsigned int x);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_smul_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_21c7d9cbb050990055f10e0fc57d9fc2[30] = "llvm-examples/shemer/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_1970e77da30022a9f7f157d5e3fa5a60 = {"llvm-examples/shemer/right.rs", "\035\000\000\000\000\000\000\000\v\000\000\000\t\000\000\000"};
struct literal_struct_1 alloc_1462d87ec7fbc2eb2bc1374eb756eca7 = {"llvm-examples/shemer/right.rs", "\035\000\000\000\000\000\000\000\b\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_b8e334f92a200664aac6dc1f0546a996 = {"llvm-examples/shemer/right.rs", "\035\000\000\000\000\000\000\000\t\000\000\000\r\000\000\000"};
void right(unsigned int x) {
    char z[4];
    char i[4];
    char y[4];
    struct literal_struct_0 call3;
    struct literal_struct_0 call4;
    struct literal_struct_0 call5;
    *(unsigned int *)(&z) = x;
    *(unsigned int *)(&y) = 0U;
    *(unsigned int *)(&i) = 0U;
    if ((int)(*(unsigned int *)(&i)) >= (int)x) {
        call3 = llvm_smul_with_overflow_i32(*(unsigned int *)(&y), 2U);
    }
    if ((int)(*(unsigned int *)(&i)) >= (int)x && !call3.field1) {
        *(unsigned int *)(&y) = call3.field0;
        return;
    }
    if ((int)(*(unsigned int *)(&i)) >= (int)x && call3.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_1970e77da30022a9f7f157d5e3fa5a60);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)x) {
        call4 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&y), x);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)x && !call4.field1) {
        *(unsigned int *)(&y) = call4.field0;
        call5 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&i), 1U);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)x && !call5.field1 && !call4.field1) {
        *(unsigned int *)(&i) = call5.field0;
    }
    if ((int)(*(unsigned int *)(&i)) < (int)x && call5.field1 && !call4.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_b8e334f92a200664aac6dc1f0546a996);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)x && call4.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_1462d87ec7fbc2eb2bc1374eb756eca7);
    }
}
