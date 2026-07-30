void right(void *a, void *b) {
    int n;
    int b_var1;
    int a_var2;
    int d;
    int j;
    long val5;
    long val6;
    long val7;
    long val8;
    a_var2 = a;
    b_var1 = b;
    n = 20;
    j = 1;
    llvm_memset_p0_i64(&d, 0, 84, 0);
    ((int *)(&d))[1] = *((int *)b);
    if (j > 19) {
        ((int *)b)[20] = ((int *)a)[20];
    } else {
        val5 = j;
    }
    if (j <= 19 && val5 >= 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 21, &alloc_0b8d4325adacc96c98125829e397f6bf);
    }
    if (j <= 19 && val5 < 21) {
        val6 = j;
    }
    if (j <= 19 && val5 < 21 && val6 >= 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 21, &alloc_e08b8f2b0a3e293c3668d56d940f8468);
    }
    if (j <= 19 && val5 < 21 && val6 < 21) {
        ((int *)b)[val6] = ((int *)a)[val5];
        val7 = j;
    }
    if (j <= 19 && val5 < 21 && val6 < 21 && val7 >= 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 21, &alloc_cc41d17d5a9f127d988c0a9be0945e9f);
    }
    if (j <= 19 && val7 < 21 && val5 < 21 && val6 < 21) {
        val8 = j + 1;
    }
    if (j <= 19 && val7 < 21 && val5 < 21 && val8 >= 21 && val6 < 21) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 21, &alloc_2a88a997bb9f1e7a11884c35234a2edc);
    }
    if (j <= 19 && val7 < 21 && val8 < 21 && val5 < 21 && val6 < 21) {
        ((int *)(&d))[val8] = ((int *)b)[val7];
        j = j + 1;
    }
}
