int _RNvCs7Hul5VkTjfJ_5right1f(int x) {
    return x;
}
void right(void *a) {
    int n;
    int m;
    int a_var2;
    int j;
    int i;
    int call5;
    long val6;
    long val7;
    a_var2 = a;
    m = 10;
    n = 10;
    i = 0;
    if (i >= 10) {
    } else {
        j = 0;
    }
    if (i < 10 && j >= 10) {
        i = i + 1;
    }
    if (i < 10 && j < 10) {
        call5 = _RNvCs7Hul5VkTjfJ_5right1f((i * 10 + j));
        val6 = i;
    }
    if (i < 10 && j < 10 && val6 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 10, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (i < 10 && val6 < 10 && j < 10) {
        val7 = j;
    }
    if (i < 10 && val6 < 10 && val7 >= 10 && j < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 10, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (i < 10 && val6 < 10 && j < 10 && val7 < 10) {
        ((int *)(&((int (*)[10])a)[val6]))[val7] = call5;
        j = j + 1;
    }
}
