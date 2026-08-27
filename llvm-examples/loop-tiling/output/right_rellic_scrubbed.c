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
    *(unsigned long *)(&m) = 10;
    *(unsigned long *)(&n) = 10;
    *(unsigned long *)(&i) = 0;
    if (*(unsigned long *)(&i) >= 10) {
    } else {
        *(unsigned long *)(&j) = 0;
    }
    if (*(unsigned long *)(&i) < 10 && *(unsigned long *)(&j) >= 10) {
        *(unsigned long *)(&i) = *(unsigned long *)(&i) + 1;
    }
    if (*(unsigned long *)(&i) < 10 && *(unsigned long *)(&j) < 10) {
        call5 = _RNvCs7Hul5VkTjfJ_5right1f((unsigned int)(*(unsigned long *)(&i) * 10 + *(unsigned long *)(&j)));
        val6 = *(unsigned long *)(&i);
    }
    if (*(unsigned long *)(&i) < 10 && *(unsigned long *)(&j) < 10 && val6 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 10, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (*(unsigned long *)(&i) < 10 && val6 < 10 && *(unsigned long *)(&j) < 10) {
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10 && val6 < 10 && val7 >= 10 && *(unsigned long *)(&j) < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 10, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (*(unsigned long *)(&i) < 10 && val6 < 10 && *(unsigned long *)(&j) < 10 && val7 < 10) {
        ((unsigned int *)(&((unsigned int (*)[10])a)[val6]))[val7] = call5;
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1;
    }
}
