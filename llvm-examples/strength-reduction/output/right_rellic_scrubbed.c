void right(unsigned int B, unsigned int C, unsigned int N, unsigned int arg3);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_2652009fdce8cead498d02c3a4390b1c[42] = "llvm-examples/strength-reduction/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_9f367a284bc7ea6fe89f1d5657f4acbf = {"llvm-examples/strength-reduction/right.rs", ")\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_3dba4606618aabb57e752e345bfeb066 = {"llvm-examples/strength-reduction/right.rs", ")\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_d3a84c47372a35600e143e3b1bb6ea38 = {"llvm-examples/strength-reduction/right.rs", ")\000\000\000\000\000\000\000\b\000\000\000\r\000\000\000"};
void right(unsigned int B, unsigned int C, unsigned int N, unsigned int arg3) {
    char N_var0[4];
    char C_var1[4];
    char B_var2[4];
    char j[4];
    char i[4];
    char x[4];
    struct literal_struct_0 call6;
    struct literal_struct_0 call7;
    struct literal_struct_0 call8;
    *(unsigned int *)(&x) = arg3;
    *(unsigned int *)(&B_var2) = B;
    *(unsigned int *)(&C_var1) = C;
    *(unsigned int *)(&N_var0) = N;
    *(unsigned int *)(&i) = 0U;
    *(unsigned int *)(&j) = C;
    if ((int)(*(unsigned int *)(&i)) >= (int)N) {
    } else {
        call6 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&x), *(unsigned int *)(&j));
    }
    if ((int)(*(unsigned int *)(&i)) < (int)N && !call6.field1) {
        *(unsigned int *)(&x) = call6.field0;
        call7 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&j), B);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)N && !call7.field1 && !call6.field1) {
        *(unsigned int *)(&j) = call7.field0;
        call8 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&i), 1U);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)N && !call7.field1 && !call8.field1 && !call6.field1) {
        *(unsigned int *)(&i) = call8.field0;
    }
    if ((int)(*(unsigned int *)(&i)) < (int)N && !call7.field1 && !call6.field1 && call8.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_d3a84c47372a35600e143e3b1bb6ea38);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)N && !call6.field1 && call7.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_3dba4606618aabb57e752e345bfeb066);
    }
    if ((int)(*(unsigned int *)(&i)) < (int)N && call6.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_9f367a284bc7ea6fe89f1d5657f4acbf);
    }
}
