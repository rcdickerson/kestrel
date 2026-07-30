void right(void *a, unsigned int val);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
char alloc_d6ea669b398674e760a68487fbb40ba5[36] = "llvm-examples/array-insert/right.rs\000";
struct literal_struct_0 {
    void *field0;
    char field1[16];
};
struct literal_struct_0 alloc_1b6aad345a552ecadc4ef2f80a0f897d = {"llvm-examples/array-insert/right.rs", "#\000\000\000\000\000\000\000\006\000\000\000\031\000\000\000"};
struct literal_struct_0 alloc_a74a36876f5d89ac1dedf5b0e55c3dda = {"llvm-examples/array-insert/right.rs", "#\000\000\000\000\000\000\000\v\000\000\000\005\000\000\000"};
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
    *(unsigned long *)(&a_size) = 10UL;
    *(unsigned long *)(&j) = 0UL;
    if (*(unsigned long *)(&j) < 10UL) {
        val6 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10UL && val6 >= 11UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 11UL, &alloc_1b6aad345a552ecadc4ef2f80a0f897d);
    }
    if (!(val6 >= 11UL || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10UL) || *(unsigned long *)(&j) >= 10UL) {
        *(unsigned long *)(&len) = 11UL;
        val5 = *(unsigned long *)(&j);
    }
    if (val5 >= 11UL && (!(val6 >= 11UL || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10UL) || *(unsigned long *)(&j) >= 10UL)) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 11UL, &alloc_a74a36876f5d89ac1dedf5b0e55c3dda);
    }
    if ((!(val6 >= 11UL || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10UL) || *(unsigned long *)(&j) >= 10UL) && val5 < 11UL) {
        ((unsigned int *)a)[val5] = val;
        while (*(unsigned long *)(&j) < 11UL)
            {
                *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1UL;
            }
    }
    if ((!(val6 >= 11UL || (int)(((unsigned int *)a)[val6]) < (int)val || *(unsigned long *)(&j) >= 10UL) || *(unsigned long *)(&j) >= 10UL) && val5 < 11UL && *(unsigned long *)(&j) >= 11UL) {
        return;
    }
    if (*(unsigned long *)(&j) < 10UL && val6 < 11UL && (int)(((unsigned int *)a)[val6]) < (int)val) {
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1UL;
    }
}
