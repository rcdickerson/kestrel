void right(unsigned int arg0, unsigned int b);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_smul_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_d58fd7249401e5d7b0f8a03dedaf138b[34] = "llvm-examples/square-sum/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_179c49ada6cb72719bfa512ac4b1923a = {"llvm-examples/square-sum/right.rs", "!\000\000\000\000\000\000\000\005\000\000\000\021\000\000\000"};
struct literal_struct_1 alloc_08ea59b51ec41ad24b2b5eec37f3909f = {"llvm-examples/square-sum/right.rs", "!\000\000\000\000\000\000\000\005\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_ec107ee395ac6b4ecf0fa2ec2dc85880 = {"llvm-examples/square-sum/right.rs", "!\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
void right(unsigned int arg0, unsigned int b) {
    char b_var0[4];
    char c[4];
    char a[4];
    struct literal_struct_0 call3;
    struct literal_struct_0 call4;
    struct literal_struct_0 call5;
    *(unsigned int *)(&a) = arg0;
    *(unsigned int *)(&b_var0) = b;
    *(unsigned int *)(&c) = 0U;
    if ((int)(*(unsigned int *)(&a)) >= (int)b) {
        return;
    } else {
        call3 = llvm_smul_with_overflow_i32(*(unsigned int *)(&a), *(unsigned int *)(&a));
    }
    if ((int)(*(unsigned int *)(&a)) < (int)b && !call3.field1) {
        call4 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&c), call3.field0);
    }
    if ((int)(*(unsigned int *)(&a)) < (int)b && !call4.field1 && !call3.field1) {
        *(unsigned int *)(&c) = call4.field0;
        call5 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&a), 1U);
    }
    if ((int)(*(unsigned int *)(&a)) < (int)b && !call4.field1 && !call5.field1 && !call3.field1) {
        *(unsigned int *)(&a) = call5.field0;
    }
    if ((int)(*(unsigned int *)(&a)) < (int)b && !call4.field1 && !call3.field1 && call5.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_ec107ee395ac6b4ecf0fa2ec2dc85880);
    }
    if ((int)(*(unsigned int *)(&a)) < (int)b && !call3.field1 && call4.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_08ea59b51ec41ad24b2b5eec37f3909f);
    }
    if ((int)(*(unsigned int *)(&a)) < (int)b && call3.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_179c49ada6cb72719bfa512ac4b1923a);
    }
}
