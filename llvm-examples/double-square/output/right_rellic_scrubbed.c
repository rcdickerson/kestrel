void right(unsigned int x);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_smul_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
struct literal_struct_0 llvm_ssub_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(void *arg0);
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_0a26641f01b909b1bcb4846ddacf2dea[37] = "llvm-examples/double-square/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_4c064889032aecdd7eb938f0d2b843a2 = {"llvm-examples/double-square/right.rs", "$\000\000\000\000\000\000\000\003\000\000\000\021\000\000\000"};
struct literal_struct_1 alloc_a67e29adf6a66efea0f5854ca0e759d3 = {"llvm-examples/double-square/right.rs", "$\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_23096a9f68e7ede8cb6db28b098d0be3 = {"llvm-examples/double-square/right.rs", "$\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};
void right(unsigned int x) {
    char x_var0[4];
    char y[4];
    char z[4];
    struct literal_struct_0 call3;
    struct literal_struct_0 call4;
    struct literal_struct_0 call5;
    *(unsigned int *)(&x_var0) = x;
    call3 = llvm_smul_with_overflow_i32(2U, x);
    if (!call3.field1) {
        *(unsigned int *)(&z) = call3.field0;
        *(unsigned int *)(&y) = 0U;
    }
    if (!call3.field1 && (int)(*(unsigned int *)(&z)) <= 0) {
    }
    if (!call3.field1 && (int)(*(unsigned int *)(&z)) > 0) {
        call4 = llvm_ssub_with_overflow_i32(*(unsigned int *)(&z), 1U);
    }
    if (!call3.field1 && (int)(*(unsigned int *)(&z)) > 0 && !call4.field1) {
        *(unsigned int *)(&z) = call4.field0;
        call5 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&y), x);
    }
    if (!call3.field1 && (int)(*(unsigned int *)(&z)) > 0 && !call4.field1 && !call5.field1) {
        *(unsigned int *)(&y) = call5.field0;
    }
    if (!call3.field1 && (int)(*(unsigned int *)(&z)) > 0 && call5.field1 && !call4.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_23096a9f68e7ede8cb6db28b098d0be3);
    }
    if (!call3.field1 && (int)(*(unsigned int *)(&z)) > 0 && call4.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_a67e29adf6a66efea0f5854ca0e759d3);
    }
    if (call3.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_4c064889032aecdd7eb938f0d2b843a2);
    }
}
