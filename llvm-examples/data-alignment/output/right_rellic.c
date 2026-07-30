void right(unsigned int x);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_rem_overflow(void *arg0);
char alloc_9145327e5a54bbfe006b4c2d25b2b018[38] = "llvm-examples/data-alignment/right.rs\000";
struct literal_struct_0 {
    void *field0;
    char field1[16];
};
struct literal_struct_0 alloc_6f6e251c8165b2b3ad25bd67f27acacb = {"llvm-examples/data-alignment/right.rs", "%\000\000\000\000\000\000\000\b\000\000\000\f\000\000\000"};
void right(unsigned int x) {
    char x_var0[4];
    char w[4];
    char z[4];
    char y[4];
    unsigned int val4;
    *(unsigned int *)(&x_var0) = x;
    *(unsigned int *)(&y) = x;
    *(unsigned int *)(&z) = 16U;
    *(unsigned int *)(&w) = 0U;
    if ((int)(*(unsigned int *)(&y)) <= 4) {
        return;
    } else {
        val4 = *(unsigned int *)(&w);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !(0U && val4 == 2147483648U)) {
        if ((int)val4 % 3 == 0U) {
            *(unsigned int *)(&z) = *(unsigned int *)(&z) * 2U;
            *(unsigned int *)(&y) = *(unsigned int *)(&y) - 1U;
        }
        *(unsigned int *)(&w) = *(unsigned int *)(&w) + 1U;
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && 0U && val4 == 2147483648U) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_rem_overflow(&alloc_6f6e251c8165b2b3ad25bd67f27acacb);
    }
}
