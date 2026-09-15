unsigned int _RNvCs7Hul5VkTjfJ_5right1f(unsigned int x);
void right(void *a);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
char alloc_73bde3e7b336b23eb02372fcd1f1cbca[35] = "llvm-examples/loop-tiling/right.rs\000";
struct literal_struct_0 {
    void *field0;
    char field1[16];
};
struct literal_struct_0 alloc_a549888368d39939078ca63aa1dda3a4 = {"llvm-examples/loop-tiling/right.rs", "\"\000\000\000\000\000\000\000\v\000\000\000\r\000\000\000"};
unsigned int _RNvCs7Hul5VkTjfJ_5right1f(unsigned int x) {
    char x_var0[4];
    *(unsigned int *)(&x_var0) = x;
    return x;
}
void right(void *a) {
    char n[8];
    char m[8];
    char a_var2[8];
    char j[8];
    char i[8];
    unsigned int call5;
    unsigned long val6;
    unsigned long val7;
    *(void **)(&a_var2) = a;
    *(unsigned long *)(&m) = 10UL;
    *(unsigned long *)(&n) = 10UL;
    *(unsigned long *)(&i) = 0UL;
    if (*(unsigned long *)(&i) >= 10UL) {
        return;
    } else {
        *(unsigned long *)(&j) = 0UL;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) >= 10UL) {
        *(unsigned long *)(&i) = *(unsigned long *)(&i) + 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL) {
        call5 = _RNvCs7Hul5VkTjfJ_5right1f((unsigned int)(*(unsigned long *)(&i) * 10UL + *(unsigned long *)(&j)));
        val6 = *(unsigned long *)(&i);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL && val6 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 10UL, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (*(unsigned long *)(&i) < 10UL && val6 < 10UL && *(unsigned long *)(&j) < 10UL) {
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10UL && val6 < 10UL && val7 >= 10UL && *(unsigned long *)(&j) < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 10UL, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (*(unsigned long *)(&i) < 10UL && val6 < 10UL && *(unsigned long *)(&j) < 10UL && val7 < 10UL) {
        ((unsigned int *)(&((unsigned int (*)[10])a)[val6]))[val7] = call5;
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1UL;
    }
}
