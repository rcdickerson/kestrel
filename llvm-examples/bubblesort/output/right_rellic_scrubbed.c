void right(void *a) {
    int temp;
    int n;
    int a_var2;
    int j;
    int i;
    long val5;
    long val6;
    long val7;
    float val8;
    long val9;
    long val10;
    long val11;
    a_var2 = a;
    n = 10;
    i = 0;
    if (i >= 10) {
    } else {
        j = 9;
    }
    if (i < 10 && j <= i) {
        i = i + 1;
    }
    if (i < 10 && j > i) {
        val5 = j - 1;
    }
    if (i < 10 && j > i && val5 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 10, &alloc_d10824f57abd82b96f74d8a998900e37);
    }
    if (i < 10 && val5 < 10 && j > i) {
        val6 = j;
    }
    if (i < 10 && val5 < 10 && j > i && val6 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 10, &alloc_c1472aaa99a0c9e01c4370a339afe9b1);
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6]) {
        val7 = j;
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val7 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 10, &alloc_b306f3c5835633be8c030b2750cb09fc);
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val7 < 10) {
        val8 = ((float *)a)[val7];
        temp = val8;
        val9 = j - 1;
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val7 < 10 && val9 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 10, &alloc_a026c78e675b1169ca6570e96453f0ba);
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 < 10 && val7 < 10) {
        val10 = j;
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val10 >= 10 && val9 < 10 && val7 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val10, 10, &alloc_991cfbf1566089e55fc7fedefbf4d17b);
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val10 < 10 && val9 < 10 && val7 < 10) {
        ((float *)a)[val10] = ((float *)a)[val9];
        val11 = j - 1;
    }
    if (i < 10 && val5 < 10 && val11 >= 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val10 < 10 && val9 < 10 && val7 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 10, &alloc_a660e85f91318953292432dd99f84179);
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val10 < 10 && val9 < 10 && val7 < 10 && val11 < 10) {
        ((float *)a)[val11] = val8;
    }
    if (i < 10 && val5 < 10 && j > i && val6 < 10 && (((float *)a)[val5] > ((float *)a)[val6] && val10 < 10 && val9 < 10 && val7 < 10 && val11 < 10 || ((float *)a)[val5] <= ((float *)a)[val6])) {
        j = j - 1;
    }
}
