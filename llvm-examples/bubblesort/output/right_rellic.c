void right(void *a);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(void *arg0);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
char alloc_ea4d054be0d9a3464770d70d8a04499f[34] = "llvm-examples/bubblesort/right.rs\000";
struct literal_struct_0 {
    void *field0;
    char field1[16];
};
struct literal_struct_0 alloc_34f116951b3139e0475b22d64721cd95 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\017\000\000\000\r\000\000\000"};
struct literal_struct_0 alloc_be3df31bfac85ed52922cd5732d661a4 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\b\000\000\000\022\000\000\000"};
struct literal_struct_0 alloc_d10824f57abd82b96f74d8a998900e37 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\b\000\000\000\020\000\000\000"};
struct literal_struct_0 alloc_c1472aaa99a0c9e01c4370a339afe9b1 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\b\000\000\000\033\000\000\000"};
struct literal_struct_0 alloc_b306f3c5835633be8c030b2750cb09fc = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\t\000\000\000\034\000\000\000"};
struct literal_struct_0 alloc_4f931d104c31d01a560c19bd84f5d18a = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\n\000\000\000\032\000\000\000"};
struct literal_struct_0 alloc_a026c78e675b1169ca6570e96453f0ba = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\n\000\000\000\030\000\000\000"};
struct literal_struct_0 alloc_991cfbf1566089e55fc7fedefbf4d17b = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\n\000\000\000\021\000\000\000"};
struct literal_struct_0 alloc_fdc502087845ea559e5dc1b3482c0afa = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\v\000\000\000\023\000\000\000"};
struct literal_struct_0 alloc_a660e85f91318953292432dd99f84179 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\v\000\000\000\021\000\000\000"};
struct literal_struct_0 alloc_67f55a38de7b934450274c42c32973d8 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\r\000\000\000\021\000\000\000"};
void right(void *a) {
    char temp[4];
    char n[8];
    char a_var2[8];
    char j[8];
    char i[8];
    unsigned long val5;
    unsigned long val6;
    unsigned long val7;
    unsigned long val8;
    unsigned long val9;
    unsigned long val10;
    unsigned long val11;
    float val12;
    unsigned long val13;
    unsigned long val14;
    unsigned long val15;
    unsigned long val16;
    unsigned long val17;
    *(void **)(&a_var2) = a;
    *(unsigned long *)(&n) = 10UL;
    *(unsigned long *)(&i) = 0UL;
    if (*(unsigned long *)(&i) >= 10UL) {
        return;
    } else {
        *(unsigned long *)(&j) = 9UL;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) <= *(unsigned long *)(&i)) {
        val5 = *(unsigned long *)(&i);
        val6 = val5 + 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) <= *(unsigned long *)(&i) && val6 >= val5) {
        *(unsigned long *)(&i) = val6;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) <= *(unsigned long *)(&i) && val6 < val5) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_34f116951b3139e0475b22d64721cd95);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i)) {
        val7 = *(unsigned long *)(&j);
        val8 = val7 - 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 10UL, &alloc_d10824f57abd82b96f74d8a998900e37);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL) {
        val9 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 >= 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 10UL, &alloc_c1472aaa99a0c9e01c4370a339afe9b1);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL && ((float *)a)[val8] > ((float *)a)[val9]) {
        val11 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL && val11 >= 10UL && ((float *)a)[val8] > ((float *)a)[val9]) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 10UL, &alloc_b306f3c5835633be8c030b2750cb09fc);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9]) {
        val12 = ((float *)a)[val11];
        *(float *)(&temp) = val12;
        val13 = *(unsigned long *)(&j);
        val14 = val13 - 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val13 >= 1UL && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9] && val14 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val14, 10UL, &alloc_a026c78e675b1169ca6570e96453f0ba);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val13 >= 1UL && val14 < 10UL && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9]) {
        val15 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val13 >= 1UL && val14 < 10UL && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9] && val15 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val15, 10UL, &alloc_991cfbf1566089e55fc7fedefbf4d17b);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val15 < 10UL && val13 >= 1UL && val14 < 10UL && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9]) {
        ((float *)a)[val15] = ((float *)a)[val14];
        val16 = *(unsigned long *)(&j);
        val17 = val16 - 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val15 < 10UL && val13 >= 1UL && val14 < 10UL && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9] && val16 >= 1UL && val17 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val17, 10UL, &alloc_a660e85f91318953292432dd99f84179);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val15 < 10UL && val13 >= 1UL && val14 < 10UL && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9] && val16 >= 1UL && val17 < 10UL) {
        ((float *)a)[val17] = val12;
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL && (((float *)a)[val8] <= ((float *)a)[val9] || !(val13 < 1UL || ((float *)a)[val8] <= ((float *)a)[val9] || val11 >= 10UL || val15 >= 10UL || val14 >= 10UL || val17 >= 10UL || val16 < 1UL))) {
        val10 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL && val10 >= 1UL && (((float *)a)[val8] <= ((float *)a)[val9] || !(val13 < 1UL || ((float *)a)[val8] <= ((float *)a)[val9] || val11 >= 10UL || val15 >= 10UL || val14 >= 10UL || val17 >= 10UL || val16 < 1UL))) {
        *(unsigned long *)(&j) = val10 - 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL && val10 < 1UL && (((float *)a)[val8] <= ((float *)a)[val9] || !(val13 < 1UL || ((float *)a)[val8] <= ((float *)a)[val9] || val11 >= 10UL || val15 >= 10UL || val14 >= 10UL || val17 >= 10UL || val16 < 1UL))) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_67f55a38de7b934450274c42c32973d8);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val15 < 10UL && val13 >= 1UL && val14 < 10UL && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9] && val16 < 1UL) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_fdc502087845ea559e5dc1b3482c0afa);
    }
    if (*(unsigned long *)(&i) < 10UL && val9 < 10UL && val13 < 1UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 >= 1UL && val8 < 10UL && val11 < 10UL && ((float *)a)[val8] > ((float *)a)[val9]) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_4f931d104c31d01a560c19bd84f5d18a);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) > *(unsigned long *)(&i) && val7 < 1UL) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_be3df31bfac85ed52922cd5732d661a4);
    }
}
