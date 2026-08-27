void right(void *a) {
    char temp[4];
    char n[8];
    char a_var2[8];
    char j[8];
    char i[8];
    unsigned long val5;
    unsigned long val6;
    unsigned long val7;
    float val8;
    unsigned long val9;
    unsigned long val10;
    unsigned long val11;
    *(void **)(&a_var2) = a;
    *(unsigned long *)(&n) = 10;
    *(unsigned long *)(&i) = 0;
    if (*(unsigned long *)(&i) >= 10) {
    } else {
        *(unsigned long *)(&j) = 9;
    }
    if (*(unsigned long *)(&i) < 10 && *(unsigned long *)(&j) <= *(unsigned long *)(&i)) {
        *(unsigned long *)(&i) = *(unsigned long *)(&i) + 1;
    }
    if (*(unsigned long *)(&i) < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i)) {
        val5 = *(unsigned long *)(&j) - 1;
    }
    if (*(unsigned long *)(&i) < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val5 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 10, &alloc_d10824f57abd82b96f74d8a998900e37);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i)) {
        val6 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && val6 >= 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i)) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 10, &alloc_c1472aaa99a0c9e01c4370a339afe9b1);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6]) {
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val7 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 10, &alloc_b306f3c5835633be8c030b2750cb09fc);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6]) {
        val8 = ((float *)a)[val7];
        *(float *)(&temp) = val8;
        val9 = *(unsigned long *)(&j) - 1;
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 10, &alloc_a026c78e675b1169ca6570e96453f0ba);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 < 10) {
        val10 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 < 10 && val10 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val10, 10, &alloc_991cfbf1566089e55fc7fedefbf4d17b);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 < 10 && val10 < 10) {
        ((float *)a)[val10] = ((float *)a)[val9];
        val11 = *(unsigned long *)(&j) - 1;
    }
    if (*(unsigned long *)(&i) < 10 && val11 >= 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 < 10 && val10 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 10, &alloc_a660e85f91318953292432dd99f84179);
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 < 10 && val10 < 10 && val11 < 10) {
        ((float *)a)[val11] = val8;
    }
    if (*(unsigned long *)(&i) < 10 && val5 < 10 && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val6 < 10 && (((float *)a)[val5] <= ((float *)a)[val6] || val7 < 10 && ((float *)a)[val5] > ((float *)a)[val6] && val9 < 10 && val10 < 10 && val11 < 10)) {
        *(unsigned long *)(&j) = *(unsigned long *)(&j) - 1;
    }
}
