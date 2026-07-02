unsigned int _ZN10arithmetic7compute17ha86421f09ea0b53eE(unsigned int a, unsigned int b, unsigned int c);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
struct literal_struct_0 llvm_smul_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
char alloc_899392582b7fde1bab3c6663c0b7cee1[39] = "llvm-examples/arithmetic/arithmetic.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_9b398cbf6e12c203b55e61d4308a0691 = {"llvm-examples/arithmetic/arithmetic.rs", "&\000\000\000\000\000\000\000\002\000\000\000\017\000\000\000"};
struct literal_struct_1 alloc_3f2ff58dc16902889f3ba955cd8b5da9 = {"llvm-examples/arithmetic/arithmetic.rs", "&\000\000\000\000\000\000\000\003\000\000\000\020\000\000\000"};
unsigned int _ZN10arithmetic7compute17ha86421f09ea0b53eE(unsigned int a, unsigned int b, unsigned int c) {
    struct literal_struct_0 call0;
    struct literal_struct_0 call1;
    call0 = llvm_sadd_with_overflow_i32(a, b);
    if (!call0.field1) {
        call1 = llvm_smul_with_overflow_i32(call0.field0, c);
    }
    if (!call0.field1 && !call1.field1) {
        return call1.field0;
    }
    if (!call0.field1 && call1.field1) {
        _RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_3f2ff58dc16902889f3ba955cd8b5da9);
    }
    if (call0.field1) {
        _RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(&alloc_9b398cbf6e12c203b55e61d4308a0691);
    }
}
