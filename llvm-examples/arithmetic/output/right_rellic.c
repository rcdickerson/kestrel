void right(unsigned int a, unsigned int b, unsigned int c);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
struct literal_struct_0 llvm_smul_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
char alloc_28b8e771a7726746841cf729893543f2[34] = "llvm-examples/arithmetic/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_ddd654ef6743487b57c8fe6f246f34b4 = {"llvm-examples/arithmetic/right.rs", "!\000\000\000\000\000\000\000\002\000\000\000\017\000\000\000"};
struct literal_struct_1 alloc_d514bf3b79539a2c02294e96e23f2c88 = {"llvm-examples/arithmetic/right.rs", "!\000\000\000\000\000\000\000\003\000\000\000\020\000\000\000"};
void right(unsigned int a, unsigned int b, unsigned int c) {
    char prod[4];
    char sum[4];
    char c_var2[4];
    char b_var3[4];
    char a_var4[4];
    struct literal_struct_0 call5;
    unsigned int val6;
    struct literal_struct_0 call7;
    *(unsigned int *)(&a_var4) = a;
    *(unsigned int *)(&b_var3) = b;
    *(unsigned int *)(&c_var2) = c;
    call5 = llvm_sadd_with_overflow_i32(a, b);
    val6 = call5.field0;
    if (!call5.field1) {
        *(unsigned int *)(&sum) = val6;
        call7 = llvm_smul_with_overflow_i32(val6, c);
    }
    if (!call5.field1 && !call7.field1) {
        *(unsigned int *)(&prod) = call7.field0;
        return;
    }
    if (!call5.field1 && call7.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_d514bf3b79539a2c02294e96e23f2c88);
    }
    if (call5.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_ddd654ef6743487b57c8fe6f246f34b4);
    }
}
