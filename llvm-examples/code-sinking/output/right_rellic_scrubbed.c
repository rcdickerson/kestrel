void right(void *a);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_bf44ca51fc47be80b8773cb414d76a9d[36] = "llvm-examples/code-sinking/right.rs\000";
struct literal_struct_0 {
    void *field0;
    char field1[16];
};
struct literal_struct_0 alloc_b6a9a667e486e61363affc1a8f96404f = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\r\000\000\000\022\000\000\000"};
struct literal_struct_0 alloc_25839b1997cb2d6209d8d3c6ba0567b5 = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\016\000\000\000\023\000\000\000"};
struct literal_struct_0 alloc_f8b2f46ae7d9d9573fbd43ab55b46be9 = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\024\000\000\000\r\000\000\000"};
struct literal_struct_0 alloc_caa79b646cf59bcf219f4511c5e9fbeb = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\026\000\000\000\r\000\000\000"};
void right(void *a) {
    char t[4];
    char n[8];
    char a_var2[8];
    char maxi[8];
    char max[4];
    char j[8];
    unsigned long val6;
    unsigned long val7;
    unsigned long val8;
    unsigned long val9;
    unsigned int val10;
    unsigned long val11;
    *(void **)(&a_var2) = a;
    *(unsigned long *)(&n) = 10UL;
    *(unsigned long *)(&j) = 0UL;
    *(unsigned int *)(&max) = 0U;
    *(unsigned long *)(&maxi) = 0UL;
    if (*(unsigned long *)(&j) >= 10UL) {
    } else {
        if (*(unsigned long *)(&j) == 0UL) {
            *(unsigned int *)(&max) = *((unsigned int *)a);
            *(unsigned long *)(&maxi) = 0UL;
        }
        val6 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10UL && val6 >= 11UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 11UL, &alloc_b6a9a667e486e61363affc1a8f96404f);
    }
    if (*(unsigned long *)(&j) < 10UL && val6 < 11UL && (int)(*(unsigned int *)(&max)) < (int)(((unsigned int *)a)[val6])) {
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10UL && val6 < 11UL && val7 >= 11UL && (int)(*(unsigned int *)(&max)) < (int)(((unsigned int *)a)[val6])) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 11UL, &alloc_25839b1997cb2d6209d8d3c6ba0567b5);
    }
    if (*(unsigned long *)(&j) < 10UL && val7 < 11UL && val6 < 11UL && (int)(*(unsigned int *)(&max)) < (int)(((unsigned int *)a)[val6])) {
        *(unsigned int *)(&max) = ((unsigned int *)a)[val7];
        *(unsigned long *)(&maxi) = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 10UL && (val7 < 11UL || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val6 < 11UL && *(unsigned long *)(&j) == 10UL) {
        val10 = ((unsigned int *)a)[10UL];
        *(unsigned int *)(&t) = val10;
        ((unsigned int *)a)[10UL] = *(unsigned int *)(&max);
        val11 = *(unsigned long *)(&maxi);
    }
    if (*(unsigned long *)(&j) < 10UL && (val7 < 11UL || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val6 < 11UL && val11 >= 11UL && *(unsigned long *)(&j) == 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 11UL, &alloc_f8b2f46ae7d9d9573fbd43ab55b46be9);
    }
    if (*(unsigned long *)(&j) < 10UL && (val7 < 11UL || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val6 < 11UL && val11 < 11UL && *(unsigned long *)(&j) == 10UL) {
        ((unsigned int *)a)[val11] = val10;
    }
    if (*(unsigned long *)(&j) < 10UL && (val7 < 11UL || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val6 < 11UL && (*(unsigned long *)(&j) != 10UL || val11 < 11UL)) {
        val8 = *(unsigned long *)(&j);
        val9 = val8 + 1UL;
    }
    if (*(unsigned long *)(&j) < 10UL && (val7 < 11UL || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val6 < 11UL && val9 >= val8 && (*(unsigned long *)(&j) != 10UL || val11 < 11UL)) {
        *(unsigned long *)(&j) = val9;
    }
    if (*(unsigned long *)(&j) < 10UL && (val7 < 11UL || (int)(*(unsigned int *)(&max)) >= (int)(((unsigned int *)a)[val6])) && val6 < 11UL && val9 < val8 && (*(unsigned long *)(&j) != 10UL || val11 < 11UL)) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_caa79b646cf59bcf219f4511c5e9fbeb);
    }
}
