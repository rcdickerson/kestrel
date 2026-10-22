unsigned int _RNvCs7Hul5VkTjfJ_5right1f(unsigned int x);
void right(void *a);
struct literal_struct_0 {
    unsigned long field0;
    unsigned char field1;
};
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
struct literal_struct_0 llvm_umul_with_overflow_i64(unsigned long arg0, unsigned long arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
char alloc_73bde3e7b336b23eb02372fcd1f1cbca[35] = "llvm-examples/loop-tiling/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_dad866affc51c6a11cc22d96a0bd7a9d = {"llvm-examples/loop-tiling/right.rs", "\"\000\000\000\000\000\000\000\016\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_b9657f3f085e25834298a1b8ce58ca04 = {"llvm-examples/loop-tiling/right.rs", "\"\000\000\000\000\000\000\000\v\000\000\000\032\000\000\000"};
struct literal_struct_1 alloc_d856e642920ae99522851566029b1170 = {"llvm-examples/loop-tiling/right.rs", "\"\000\000\000\000\000\000\000\v\000\000\000\031\000\000\000"};
struct literal_struct_1 alloc_a549888368d39939078ca63aa1dda3a4 = {"llvm-examples/loop-tiling/right.rs", "\"\000\000\000\000\000\000\000\v\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_fdb4c44327b85399d26ef100d2b9a33e = {"llvm-examples/loop-tiling/right.rs", "\"\000\000\000\000\000\000\000\f\000\000\000\021\000\000\000"};
unsigned int _RNvCs7Hul5VkTjfJ_5right1f(unsigned int x) {
    char x_var0[4];
    *(unsigned int *)(&x_var0) = x;
    return x;
}
void right(void *a) {
    char n[8];
    char m[8];
    char a_var2[8];
    char j[8];
    char i[8];
    unsigned long val5;
    unsigned long val6;
    struct literal_struct_0 call7;
    unsigned long val8;
    unsigned long val9;
    unsigned int call10;
    unsigned long val11;
    unsigned long val12;
    unsigned long val13;
    unsigned long val14;
    *(void **)(&a_var2) = a;
    *(unsigned long *)(&m) = 10UL;
    *(unsigned long *)(&n) = 10UL;
    *(unsigned long *)(&i) = 0UL;
    if (*(unsigned long *)(&i) >= 10UL) {
    } else {
        *(unsigned long *)(&j) = 0UL;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) >= 10UL) {
        val5 = *(unsigned long *)(&i);
        val6 = val5 + 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) >= 10UL && val6 >= val5) {
        *(unsigned long *)(&i) = val6;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) >= 10UL && val6 < val5) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_dad866affc51c6a11cc22d96a0bd7a9d);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL) {
        call7 = llvm_umul_with_overflow_i64(*(unsigned long *)(&i), 10UL);
        val8 = call7.field0;
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL && !call7.field1) {
        val9 = val8 + *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL && val9 >= val8 && !call7.field1) {
        call10 = _RNvCs7Hul5VkTjfJ_5right1f((unsigned int)val9);
        val11 = *(unsigned long *)(&i);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL && val9 >= val8 && !call7.field1 && val11 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 10UL, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (*(unsigned long *)(&i) < 10UL && val11 < 10UL && *(unsigned long *)(&j) < 10UL && val9 >= val8 && !call7.field1) {
        val12 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&i) < 10UL && val11 < 10UL && *(unsigned long *)(&j) < 10UL && val9 >= val8 && val12 >= 10UL && !call7.field1) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val12, 10UL, &alloc_a549888368d39939078ca63aa1dda3a4);
    }
    if (*(unsigned long *)(&i) < 10UL && val11 < 10UL && *(unsigned long *)(&j) < 10UL && val9 >= val8 && val12 < 10UL && !call7.field1) {
        ((unsigned int *)(&((unsigned int (*)[10])a)[val11]))[val12] = call10;
        val13 = *(unsigned long *)(&j);
        val14 = val13 + 1UL;
    }
    if (*(unsigned long *)(&i) < 10UL && val11 < 10UL && *(unsigned long *)(&j) < 10UL && val9 >= val8 && val12 < 10UL && !call7.field1 && val14 >= val13) {
        *(unsigned long *)(&j) = val14;
    }
    if (*(unsigned long *)(&i) < 10UL && val14 < val13 && val11 < 10UL && *(unsigned long *)(&j) < 10UL && val9 >= val8 && val12 < 10UL && !call7.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_fdb4c44327b85399d26ef100d2b9a33e);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL && val9 < val8 && !call7.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_d856e642920ae99522851566029b1170);
    }
    if (*(unsigned long *)(&i) < 10UL && *(unsigned long *)(&j) < 10UL && call7.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_b9657f3f085e25834298a1b8ce58ca04);
    }
}
