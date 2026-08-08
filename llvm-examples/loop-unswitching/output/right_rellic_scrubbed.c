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
    unsigned long val9;
    unsigned long val10;
    unsigned long val11;
    unsigned long val12;
    unsigned long val13;
    unsigned long val14;
    unsigned long val15;
    unsigned long val16;
    unsigned long val17;
    *(void **)(&a_var5) = a;
    *(void **)(&b_var4) = b;
    *(void **)(&c_var3) = c;
    *(unsigned int *)(&k_var2) = k;
    *(unsigned int *)(&x_var1) = x;
    *(unsigned long *)(&n) = 10;
    if ((int)x >= 7) {
        *(unsigned long *)(&j) = 0;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10) {
        val8 = *(unsigned long *)(&j);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val8 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 10, &alloc_419ef0d9175c3c3d25b6349e67ee0cbd);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val8 < 10) {
        val9 = *(unsigned long *)(&j);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val8 < 10 && val9 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 10, &alloc_d2d5579a465f4b0e260596020158df10);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val8 < 10 && val9 < 10) {
        ((unsigned int *)a)[val9] = ((unsigned int *)a)[val8] + k;
        val10 = *(unsigned long *)(&j) - 1;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val10 >= 10 && val8 < 10 && val9 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val10, 10, &alloc_e3f13fad5a0fb42e992397669711c193);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val10 < 10 && val8 < 10 && val9 < 10) {
        val11 = *(unsigned long *)(&j) - 1;
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val10 < 10 && val8 < 10 && val9 < 10 && val11 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 10, &alloc_bb2f62fcbec2afd6481e273b7e37fcc1);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val10 < 10 && val8 < 10 && val9 < 10 && val11 < 10) {
        val12 = *(unsigned long *)(&j);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val10 < 10 && val8 < 10 && val9 < 10 && val11 < 10 && val12 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val12, 10, &alloc_31ffd0f23462b2f4117f2c5301d8027b);
    }
    if ((int)x >= 7 && *(unsigned long *)(&j) < 10 && val10 < 10 && val12 < 10 && val8 < 10 && val9 < 10 && val11 < 10) {
        ((unsigned int *)b)[val12] = ((unsigned int *)a)[val10] * ((unsigned int *)b)[val11];
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1;
    }
    if ((int)x < 7) {
        *(unsigned long *)(&j_var7) = 0;
    }
    if (!((int)x < 7 ? *(unsigned long *)(&j_var7) < 10 : *(unsigned long *)(&j) < 10)) {
        return;
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10) {
        val13 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val13 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val13, 10, &alloc_a431e0af1f0a773d7894a8f7648fcbbb);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val13 < 10) {
        val14 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val14 >= 10 && val13 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val14, 10, &alloc_86a95f0408d87e2b4012bd6715ad108d);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val14 < 10 && val13 < 10) {
        ((unsigned int *)a)[val14] = ((unsigned int *)a)[val13] + k;
        val15 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val14 < 10 && val13 < 10 && val15 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val15, 10, &alloc_72db5233068273f5dabaebf836ed1389);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val14 < 10 && val15 < 10 && val13 < 10) {
        val16 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && val16 >= 10 && *(unsigned long *)(&j_var7) < 10 && val14 < 10 && val15 < 10 && val13 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val16, 10, &alloc_40b9f4e097b3d8001419ebb57560c155);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val14 < 10 && val15 < 10 && val13 < 10 && val16 < 10) {
        val17 = *(unsigned long *)(&j_var7);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val14 < 10 && val17 >= 10 && val15 < 10 && val13 < 10 && val16 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val17, 10, &alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2);
    }
    if ((int)x < 7 && *(unsigned long *)(&j_var7) < 10 && val14 < 10 && val15 < 10 && val13 < 10 && val16 < 10 && val17 < 10) {
        ((unsigned int *)b)[val17] = ((unsigned int *)a)[val15] * ((unsigned int *)c)[val16];
        *(unsigned long *)(&j_var7) = *(unsigned long *)(&j_var7) + 1;
    }
}
