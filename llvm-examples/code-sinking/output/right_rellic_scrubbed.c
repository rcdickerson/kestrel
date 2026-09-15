void right(void *a) {
    char t[4];
    char n[8];
    char a_var2[8];
    char maxi[8];
    char max[4];
    char j[8];
    unsigned long val6;
    unsigned long val7;
    unsigned int val8;
    unsigned long val9;
    *(void **)(&a_var2) = a;
    *(unsigned long *)(&n) = 10;
    *(unsigned long *)(&j) = 0;
    *(unsigned int *)(&max) = 0;
    *(unsigned long *)(&maxi) = 0;
    if (*(unsigned long *)(&j) >= 10) {
    } else {
        if (*(unsigned long *)(&j) == 0) {
            *(unsigned int *)(&max) = *((unsigned int *)a);
            *(unsigned long *)(&maxi) = 0;
        }
        val6 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10 && val6 >= 11) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 11, &alloc_b6a9a667e486e61363affc1a8f96404f);
    }
    if (*(unsigned long *)(&j) < 10 && val6 < 11 && (int)(*(unsigned int *)(&max)) < (int)(((unsigned int *)a)[val6])) {
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10 && val6 < 11 && val7 >= 11 && (int)(*(unsigned int *)(&max)) < (int)(((unsigned int *)a)[val6])) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 11, &alloc_25839b1997cb2d6209d8d3c6ba0567b5);
    }
    if (*(unsigned long *)(&j) < 10 && val7 < 11 && val6 < 11 && (int)(*(unsigned int *)(&max)) < (int)(((unsigned int *)a)[val6])) {
        *(unsigned int *)(&max) = ((unsigned int *)a)[val7];
        *(unsigned long *)(&maxi) = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10 && val6 < 11 && (val7 < 11 || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && *(unsigned long *)(&j) == 10) {
        val8 = ((unsigned int *)a)[10];
        *(unsigned int *)(&t) = val8;
        ((unsigned int *)a)[10] = *(unsigned int *)(&max);
        val9 = *(unsigned long *)(&maxi);
    }
    if (*(unsigned long *)(&j) < 10 && val6 < 11 && (val7 < 11 || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val9 >= 11 && *(unsigned long *)(&j) == 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 11, &alloc_f8b2f46ae7d9d9573fbd43ab55b46be9);
    }
    if (*(unsigned long *)(&j) < 10 && val6 < 11 && (val7 < 11 || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val9 < 11 && *(unsigned long *)(&j) == 10) {
        ((unsigned int *)a)[val9] = val8;
    }
    if (*(unsigned long *)(&j) < 10 && val6 < 11 && (val7 < 11 || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && (*(unsigned long *)(&j) != 10 || val9 < 11)) {
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1;
    }
}
