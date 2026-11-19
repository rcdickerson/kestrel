void right(void *a, void *b, void *c, unsigned int k, unsigned int x);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(void *arg0);
struct literal_struct_0 llvm_smul_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
char alloc_df9fb36b3e50035d5a26429439c29ed9[40] = "llvm-examples/loop-unswitching/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_419ef0d9175c3c3d25b6349e67ee0cbd = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\016\000\000\000\024\000\000\000"};
struct literal_struct_1 alloc_d2d5579a465f4b0e260596020158df10 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\016\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_3851e86263c4f1dc61060dfc24bfb5f8 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\017\000\000\000\026\000\000\000"};
struct literal_struct_1 alloc_e3f13fad5a0fb42e992397669711c193 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\017\000\000\000\024\000\000\000"};
struct literal_struct_1 alloc_a71056d669a165115308cd734a984c01 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\017\000\000\000!\000\000\000"};
struct literal_struct_1 alloc_bb2f62fcbec2afd6481e273b7e37fcc1 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\017\000\000\000\037\000\000\000"};
struct literal_struct_1 alloc_31ffd0f23462b2f4117f2c5301d8027b = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\017\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_abbc3ba085879e0c58420fdd90df364b = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\020\000\000\000\021\000\000\000"};
struct literal_struct_1 alloc_a431e0af1f0a773d7894a8f7648fcbbb = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\a\000\000\000\024\000\000\000"};
struct literal_struct_1 alloc_86a95f0408d87e2b4012bd6715ad108d = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_72db5233068273f5dabaebf836ed1389 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\b\000\000\000\024\000\000\000"};
struct literal_struct_1 alloc_40b9f4e097b3d8001419ebb57560c155 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\b\000\000\000\033\000\000\000"};
struct literal_struct_1 alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2 = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\b\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_9a0d9beb0fd0d5747443c939bdea398d = {"llvm-examples/loop-unswitching/right.rs", "'\000\000\000\000\000\000\000\t\000\000\000\021\000\000\000"};
void right(void *a, void *b, void *c, unsigned int k, unsigned int x) {
    char n[8];
    char x_var1[4];
    char k_var2[4];
    char c_var3[8];
    char b_var4[8];
    char a_var5[8];
    char j[8];
    char j_var7[8];
    unsigned long val8;
    struct literal_struct_0 call9;
    unsigned long val10;
    unsigned long val11;
    unsigned long val12;
    unsigned long val13;
    unsigned long val14;
    struct literal_struct_0 call15;
    unsigned long val16;
    unsigned long val17;
    unsigned long val18;
    unsigned long val19;
    struct literal_struct_0 call20;
    unsigned long val21;
    unsigned long val22;
    unsigned long val23;
    struct literal_struct_0 call24;
    unsigned long val25;
    unsigned long val26;
    unsigned long val27;
    *(void **)(&a_var5) = a;
    *(void **)(&b_var4) = b;
    *(void **)(&c_var3) = c;
    *(unsigned int *)(&k_var2) = k;
    *(unsigned int *)(&x_var1) = x;
    *(unsigned long *)(&n) = 10UL;
    if ((int)x >= 7) {
        *(unsigned long *)(&j) = 0UL;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL) {
        val8 = *(unsigned long *)(&j);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val8 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 10UL, &alloc_419ef0d9175c3c3d25b6349e67ee0cbd);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val8 < 10UL) {
        call9 = llvm_sadd_with_overflow_i32(((unsigned int *)a)[val8], k);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val8 < 10UL && !call9.field1) {
        val10 = *(unsigned long *)(&j);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val8 < 10UL && !call9.field1 && val10 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val10, 10UL, &alloc_d2d5579a465f4b0e260596020158df10);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val8 < 10UL && !call9.field1) {
        ((unsigned int *)a)[val10] = call9.field0;
        val11 = *(unsigned long *)(&j);
        val12 = val11 - 1UL;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && val12 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val12, 10UL, &alloc_e3f13fad5a0fb42e992397669711c193);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && val12 < 10UL) {
        val13 = *(unsigned long *)(&j);
        val14 = val13 - 1UL;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && val12 < 10UL && val14 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val14, 10UL, &alloc_bb2f62fcbec2afd6481e273b7e37fcc1);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val14 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && val12 < 10UL) {
        call15 = llvm_smul_with_overflow_i32(((unsigned int *)a)[val12], ((unsigned int *)b)[val14]);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val14 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && !call15.field1 && val12 < 10UL) {
        val16 = *(unsigned long *)(&j);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val14 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && !call15.field1 && val12 < 10UL && val16 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val16, 10UL, &alloc_31ffd0f23462b2f4117f2c5301d8027b);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val14 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && !call15.field1 && val12 < 10UL && val16 < 10UL) {
        ((unsigned int *)b)[val16] = call15.field0;
        val17 = *(unsigned long *)(&j);
        val18 = val17 + 1UL;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val14 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && val18 >= val17 && !call15.field1 && val12 < 10UL && val16 < 10UL) {
        *(unsigned long *)(&j) = val18;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val14 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && !call15.field1 && val12 < 10UL && val18 < val17 && val16 < 10UL) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_abbc3ba085879e0c58420fdd90df364b);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 >= 1UL && val14 < 10UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && call15.field1 && val12 < 10UL) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_e3f13fad5a0fb42e992397669711c193);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val13 < 1UL && val11 >= 1UL && val8 < 10UL && !call9.field1 && val12 < 10UL) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_a71056d669a165115308cd734a984c01);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val10 < 10UL && val11 < 1UL && val8 < 10UL && !call9.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_3851e86263c4f1dc61060dfc24bfb5f8);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10UL && val8 < 10UL && call9.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_419ef0d9175c3c3d25b6349e67ee0cbd);
    }
    if ((int)x < 7) {
        *(unsigned long *)(&j_var7) = 0UL;
    }
    if (!((int)x < 7 ? *(unsigned long *)(&j_var7) < 10UL : *(unsigned long *)(&j) < 10UL)) {
        return;
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL) {
        val19 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && val19 >= 10UL && *(unsigned long *)(&j_var7) < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val19, 10UL, &alloc_a431e0af1f0a773d7894a8f7648fcbbb);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && val19 < 10UL) {
        call20 = llvm_sadd_with_overflow_i32(((unsigned int *)a)[val19], k);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val19 < 10UL) {
        val21 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 >= 10UL && val19 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val21, 10UL, &alloc_86a95f0408d87e2b4012bd6715ad108d);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL) {
        ((unsigned int *)a)[val21] = call20.field0;
        val22 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && val22 >= 10UL && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val22, 10UL, &alloc_72db5233068273f5dabaebf836ed1389);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL && val22 < 10UL) {
        val23 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL && val23 >= 10UL && val22 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val23, 10UL, &alloc_40b9f4e097b3d8001419ebb57560c155);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL && val22 < 10UL && val23 < 10UL) {
        call24 = llvm_smul_with_overflow_i32(((unsigned int *)a)[val22], ((unsigned int *)c)[val23]);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL && val22 < 10UL && val23 < 10UL && !call24.field1) {
        val25 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL && val22 < 10UL && val23 < 10UL && !call24.field1 && val25 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val25, 10UL, &alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2);
    }
    if ((int)x < 7 && val25 < 10UL && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL && val22 < 10UL && val23 < 10UL && !call24.field1) {
        ((unsigned int *)b)[val25] = call24.field0;
        val26 = *(unsigned long *)(&j_var7);
        val27 = val26 + 1UL;
    }
    if ((int)x < 7 && val25 < 10UL && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val27 >= val26 && val21 < 10UL && val19 < 10UL && val22 < 10UL && val23 < 10UL && !call24.field1) {
        *(unsigned long *)(&j_var7) = val27;
    }
    if ((int)x < 7 && val25 < 10UL && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val27 < val26 && val21 < 10UL && val19 < 10UL && val22 < 10UL && val23 < 10UL && !call24.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_9a0d9beb0fd0d5747443c939bdea398d);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && !call20.field1 && val21 < 10UL && val19 < 10UL && val22 < 10UL && val23 < 10UL && call24.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_72db5233068273f5dabaebf836ed1389);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10UL && val19 < 10UL && call20.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_a431e0af1f0a773d7894a8f7648fcbbb);
    }
}
