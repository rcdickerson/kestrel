unsigned int _ZN4loop8sum_to_n17h1dd796fbd7a45127E(unsigned int n);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_e2b9f373b3385bf1dfe1d5657c591caa[27] = "llvm-examples/loop/loop.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_ff438de2926f93a88d97a4d20a267937 = {"llvm-examples/loop/loop.rs", "\032\000\000\000\000\000\000\000\005\000\000\000\017\000\000\000"};
struct literal_struct_1 alloc_1d4ac44ac6ce4dfa37017d5355a98ab8 = {"llvm-examples/loop/loop.rs", "\032\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
unsigned int _ZN4loop8sum_to_n17h1dd796fbd7a45127E(unsigned int n) {
    char var0[4];
    char var1[4];
    struct literal_struct_0 call2;
    struct literal_struct_0 call3;
    *(unsigned int *)(&var1) = 0U;
    *(unsigned int *)(&var0) = 1U;
    if ((int)(*(unsigned int *)(&var0)) > (int)n) {
        return *(unsigned int *)(&var1);
    } else {
        call2 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&var1), *(unsigned int *)(&var0));
    }
    if ((int)(*(unsigned int *)(&var0)) <= (int)n && !call2.field1) {
        *(unsigned int *)(&var1) = call2.field0;
        call3 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&var0), 1U);
    }
    if ((int)(*(unsigned int *)(&var0)) <= (int)n && !call3.field1 && !call2.field1) {
        *(unsigned int *)(&var0) = call3.field0;
    }
    if ((int)(*(unsigned int *)(&var0)) <= (int)n && !call2.field1 && call3.field1) {
        _RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(&alloc_1d4ac44ac6ce4dfa37017d5355a98ab8);
    }
    if ((int)(*(unsigned int *)(&var0)) <= (int)n && call2.field1) {
        _RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(&alloc_ff438de2926f93a88d97a4d20a267937);
    }
}
