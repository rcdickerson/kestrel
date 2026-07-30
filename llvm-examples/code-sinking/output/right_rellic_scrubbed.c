void right(void *a) {
    int t;
    int n;
    int a_var2;
    int maxi;
    int max;
    int j;
    long val6;
    long val7;
    int val8;
    long val9;
    a_var2 = a;
    n = 10;
    j = 0;
    max = 0;
    maxi = 0;
    if (j >= 10) {
    } else {
        if (j == 0) {
            max = *((int *)a);
            maxi = 0;
        }
        val6 = j;
    }
    if (j < 10 && val6 >= 11) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 11, &alloc_b6a9a667e486e61363affc1a8f96404f);
    }
    if (j < 10 && val6 < 11 && (max) < (((int *)a)[val6])) {
        val7 = j;
    }
    if (j < 10 && val6 < 11 && val7 >= 11 && (max) < (((int *)a)[val6])) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 11, &alloc_25839b1997cb2d6209d8d3c6ba0567b5);
    }
    if (j < 10 && val7 < 11 && val6 < 11 && (max) < (((int *)a)[val6])) {
        max = ((int *)a)[val7];
        maxi = j;
    }
    if (j < 10 && (val7 < 11 || (max) >= (((int *)a)[val6])) && val6 < 11 && j == 10) {
        val8 = ((int *)a)[10];
        t = val8;
        ((int *)a)[10] = max;
        val9 = maxi;
    }
    if (j < 10 && (val7 < 11 || (max) >= (((int *)a)[val6])) && val6 < 11 && val9 >= 11 && j == 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 11, &alloc_f8b2f46ae7d9d9573fbd43ab55b46be9);
    }
    if (j < 10 && (val7 < 11 || (max) >= (((int *)a)[val6])) && val6 < 11 && j == 10 && val9 < 11) {
        ((int *)a)[val9] = val8;
    }
    if (j < 10 && (val7 < 11 || (max) >= (((int *)a)[val6])) && val6 < 11 && (j != 10 || val9 < 11)) {
        j = j + 1;
    }
}
