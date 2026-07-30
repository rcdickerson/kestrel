void right(void *a, void *b);
void llvm_memset_p0_i64(void *arg0, char arg1, unsigned long arg2, unsigned char arg3);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
char alloc_5d2ee394d6cfc9bc3d9d880d91fe8220[38] = "llvm-examples/loop-alignment/right.rs\000";
struct literal_struct_0 {
    void *field0;
    char field1[16];
};
struct literal_struct_0 alloc_0b8d4325adacc96c98125829e397f6bf = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\t\000\000\000\020\000\000\000"};
struct literal_struct_0 alloc_e08b8f2b0a3e293c3668d56d940f8468 = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\t\000\000\000\t\000\000\000"};
struct literal_struct_0 alloc_cc41d17d5a9f127d988c0a9be0945e9f = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\n\000\000\000\024\000\000\000"};
struct literal_struct_0 alloc_2a88a997bb9f1e7a11884c35234a2edc = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\n\000\000\000\t\000\000\000"};
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
    *(unsigned long *)(&n) = 20UL;
    *(unsigned long *)(&j) = 1UL;
    llvm_memset_p0_i64(&d, 0U, 84UL, 0U);
    ((unsigned int *)(&d))[1UL] = *((unsigned int *)b);
    if (*(unsigned long *)(&j) > 19UL) {
        ((unsigned int *)b)[20UL] = ((unsigned int *)a)[20UL];
        return;
    } else {
        val5 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) <= 19UL && val5 >= 21UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 21UL, &alloc_0b8d4325adacc96c98125829e397f6bf);
    }
    if (*(unsigned long *)(&j) <= 19UL && val5 < 21UL) {
        val6 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) <= 19UL && val5 < 21UL && val6 >= 21UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 21UL, &alloc_e08b8f2b0a3e293c3668d56d940f8468);
    }
    if (*(unsigned long *)(&j) <= 19UL && val5 < 21UL && val6 < 21UL) {
        ((unsigned int *)b)[val6] = ((unsigned int *)a)[val5];
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) <= 19UL && val5 < 21UL && val6 < 21UL && val7 >= 21UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 21UL, &alloc_cc41d17d5a9f127d988c0a9be0945e9f);
    }
    if (*(unsigned long *)(&j) <= 19UL && val7 < 21UL && val5 < 21UL && val6 < 21UL) {
        val8 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) <= 19UL && val7 < 21UL && val5 < 21UL && val8 >= 21UL && val6 < 21UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 21UL, &alloc_2a88a997bb9f1e7a11884c35234a2edc);
    }
    if (*(unsigned long *)(&j) <= 19UL && val7 < 21UL && val8 < 21UL && val5 < 21UL && val6 < 21UL) {
        ((unsigned int *)(&d))[val8] = ((unsigned int *)b)[val7];
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1UL;
    }
}
