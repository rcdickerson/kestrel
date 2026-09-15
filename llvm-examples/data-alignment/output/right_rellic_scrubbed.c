void right(unsigned int x) {
    char x_var0[4];
    char w[4];
    char z[4];
    char y[4];
    unsigned int val4;
    *(unsigned int *)(&x_var0) = x;
    *(unsigned int *)(&y) = x;
    *(unsigned int *)(&z) = 16;
    *(unsigned int *)(&w) = 0;
    if ((int)(*(unsigned int *)(&y)) <= 4) {
    } else {
        val4 = *(unsigned int *)(&w);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !(0 && val4 == 2147483648)) {
        if ((int)val4 % 3 == 0) {
            *(unsigned int *)(&z) = *(unsigned int *)(&z) * 2;
            *(unsigned int *)(&y) = *(unsigned int *)(&y) - 1;
        }
        *(unsigned int *)(&w) = *(unsigned int *)(&w) + 1;
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && 0 && val4 == 2147483648) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_rem_overflow(&alloc_6f6e251c8165b2b3ad25bd67f27acacb);
    }
}
