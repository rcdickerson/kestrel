void right(void *a, void *b) {
    char n[8];
    char b_var1[8];
    char a_var2[8];
    char d[84];
    char j[8];
    unsigned long val5;
    unsigned long val6;
    unsigned long val7;
    unsigned long val8;
    *(void **)(&a_var2) = a;
    *(void **)(&b_var1) = b;
    *(unsigned long *)(&n) = 20;
    *(unsigned long *)(&j) = 1;
    llvm_memset_p0_i64(&d, 0, 84, 0);
    ((unsigned int *)(&d))[1] = *((unsigned int *)b);
    if (*(unsigned long *)(&j) > 19) {
        ((unsigned int *)b)[20] = ((unsigned int *)a)[20];
    } else {
        val5 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) <= 19 && val5 >= 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 21, &alloc_0b8d4325adacc96c98125829e397f6bf);
    }
    if (*(unsigned long *)(&j) <= 19 && val5 < 21) {
        val6 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) <= 19 && val5 < 21 && val6 >= 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 21, &alloc_e08b8f2b0a3e293c3668d56d940f8468);
    }
    if (*(unsigned long *)(&j) <= 19 && val5 < 21 && val6 < 21) {
        ((unsigned int *)b)[val6] = ((unsigned int *)a)[val5];
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) <= 19 && val5 < 21 && val6 < 21 && val7 >= 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 21, &alloc_cc41d17d5a9f127d988c0a9be0945e9f);
    }
    if (*(unsigned long *)(&j) <= 19 && val7 < 21 && val5 < 21 && val6 < 21) {
        val8 = *(unsigned long *)(&j) + 1;
    }
    if (*(unsigned long *)(&j) <= 19 && val7 < 21 && val5 < 21 && val8 >= 21 && val6 < 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 21, &alloc_2a88a997bb9f1e7a11884c35234a2edc);
    }
    if (*(unsigned long *)(&j) <= 19 && val7 < 21 && val8 < 21 && val5 < 21 && val6 < 21) {
        ((unsigned int *)(&d))[val8] = ((unsigned int *)b)[val7];
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1;
    }
}
