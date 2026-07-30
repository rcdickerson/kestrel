void right(void *a, int val) {
    int len;
    int a_size;
    int val_var2;
    int a_var3;
    int j;
    long val5;
    long val6;
    a_var3 = a;
    val_var2 = val;
    a_size = 10;
    j = 0;
    if (j < 10) {
        val6 = j;
    }
    if (j < 10 && val6 >= 11) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 11, &alloc_1b6aad345a552ecadc4ef2f80a0f897d);
    }
    if (!(val6 >= 11 || (((int *)a)[val6]) < val || j >= 10) || j >= 10) {
        len = 11;
        val5 = j;
    }
    if (val5 >= 11 && (!(val6 >= 11 || (((int *)a)[val6]) < val || j >= 10) || j >= 10)) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 11, &alloc_a74a36876f5d89ac1dedf5b0e55c3dda);
    }
    if ((!(val6 >= 11 || (((int *)a)[val6]) < val || j >= 10) || j >= 10) && val5 < 11) {
        ((int *)a)[val5] = val;
        while (j < 11)
        {
            j = j + 1;
        }
    }
    if ((!(val6 >= 11 || (((int *)a)[val6]) < val || j >= 10) || j >= 10) && val5 < 11 && j >= 11) {
    }
    if (j < 10 && val6 < 11 && (((int *)a)[val6]) < val) {
        j = j + 1;
    }
}
