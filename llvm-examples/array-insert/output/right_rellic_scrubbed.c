void right(void *a, unsigned int val) {
    char len[8];
    char a_size[8];
    char val_var2[4];
    char a_var3[8];
    char j[8];
    unsigned long val5;
    unsigned long val6;
    *(void **)(&a_var3) = a;
    *(unsigned int *)(&val_var2) = val;
    *(unsigned long *)(&a_size) = 10;
    *(unsigned long *)(&j) = 0;
    if (*(unsigned long *)(&j) < 10) {
        val6 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10 && val6 >= 11) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 11, &alloc_1b6aad345a552ecadc4ef2f80a0f897d);
    }
    if (!(val6 >= 11 || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10) || *(unsigned long *)(&j) >= 10) {
        *(unsigned long *)(&len) = 11;
        val5 = *(unsigned long *)(&j);
    }
    if ((!(val6 >= 11 || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10) || *(unsigned long *)(&j) >= 10) && val5 >= 11) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 11, &alloc_a74a36876f5d89ac1dedf5b0e55c3dda);
    }
    if (val5 < 11 && (!(val6 >= 11 || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10) || *(unsigned long *)(&j) >= 10)) {
        ((unsigned int *)a)[val5] = val;
        while (*(unsigned long *)(&j) < 11)
        {
            *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1;
        }
    }
    if (val5 < 11 && *(unsigned long *)(&j) >= 11 && (!(val6 >= 11 || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10) || *(unsigned long *)(&j) >= 10)) {
    }
    if (*(unsigned long *)(&j) < 10 && val6 < 11 && (int)(((unsigned int *)a)[val6]) < (int)val) {
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1;
    }
}
