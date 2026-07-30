void right(void *a, void *b, void *c) {
    int n;
    int c_var1;
    int b_var2;
    int a_var3;
    int j;
    long val5;
    long val6;
    long val7;
    long val8;
    long val9;
    long val10;
    long val11;
    long val12;
    long val13;
    long val14;
    long val15;
    long val16;
    long val17;
    long val18;
    long val19;
    long val20;
    long val21;
    a_var3 = a;
    b_var2 = b;
    c_var1 = c;
    n = 10;
    j = 0;
    *((int *)a) = *((int *)a) + 1;
    *((int *)b) = *((int *)b) + *((int *)a);
    ((int *)a)[1] = ((int *)a)[1] + 1;
    if (j >= 8) {
        val5 = j;
    }
    if (j >= 8 && val5 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 10, &alloc_2eb431f63ae4896b066f944852c62b63);
    }
    if (j >= 8 && val5 < 10) {
        val7 = j;
    }
    if (j >= 8 && val5 < 10 && val7 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 10, &alloc_bb008af1a11188dbc0a8220f06190d73);
    }
    if (j >= 8 && val7 < 10 && val5 < 10) {
        val8 = j;
    }
    if (j >= 8 && val7 < 10 && val5 < 10 && val8 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 10, &alloc_bae3feef6ab792f9dddd1f61e8a2ced1);
    }
    if (j >= 8 && val7 < 10 && val5 < 10 && val8 < 10) {
        ((int *)c)[val8] = ((int *)c)[val5] + ((int *)b)[val7];
        val9 = j + 1;
    }
    if (j >= 8 && val7 < 10 && val9 >= 10 && val5 < 10 && val8 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 10, &alloc_44014d371c28a91d445bc935d397da88);
    }
    if (j >= 8 && val7 < 10 && val9 < 10 && val5 < 10 && val8 < 10) {
        val10 = j + 1;
    }
    if (j >= 8 && val7 < 10 && val9 < 10 && val5 < 10 && val10 >= 10 && val8 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val10, 10, &alloc_d6acdfa81a08d929191080bb8281517a);
    }
    if (j >= 8 && val7 < 10 && val9 < 10 && val5 < 10 && val8 < 10 && val10 < 10) {
        val11 = j + 1;
    }
    if (j >= 8 && val7 < 10 && val9 < 10 && val5 < 10 && val11 >= 10 && val8 < 10 && val10 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 10, &alloc_e8ea127106c26cc7ad8e0642c4b2c171);
    }
    if (j >= 8 && val11 < 10 && val7 < 10 && val9 < 10 && val5 < 10 && val8 < 10 && val10 < 10) {
        ((int *)b)[val11] = ((int *)b)[val9] + ((int *)a)[val10];
        val12 = j + 1;
    }
    if (j >= 8 && val11 < 10 && val7 < 10 && val12 >= 10 && val9 < 10 && val5 < 10 && val8 < 10 && val10 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val12, 10, &alloc_09ab0c4698002ff1be2861a2d737e0f9);
    }
    if (j >= 8 && val11 < 10 && val7 < 10 && val12 < 10 && val9 < 10 && val5 < 10 && val8 < 10 && val10 < 10) {
        val13 = j + 1;
    }
    if (j >= 8 && val11 < 10 && val7 < 10 && val12 < 10 && val9 < 10 && val5 < 10 && val8 < 10 && val10 < 10 && val13 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val13, 10, &alloc_a99a5d4cc55dcc51ad4c685788710a5b);
    }
    if (j >= 8 && val11 < 10 && val7 < 10 && val12 < 10 && val9 < 10 && val5 < 10 && val8 < 10 && val10 < 10 && val13 < 10) {
        val14 = j + 1;
    }
    if (j >= 8 && val11 < 10 && val7 < 10 && val12 < 10 && val9 < 10 && val5 < 10 && val8 < 10 && val10 < 10 && val13 < 10 && val14 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val14, 10, &alloc_68b2bf2a0742d809e57390f761e71dad);
    }
    if (j >= 8 && val11 < 10 && val7 < 10 && val12 < 10 && val9 < 10 && val5 < 10 && val8 < 10 && val14 < 10 && val10 < 10 && val13 < 10) {
        ((int *)c)[val14] = ((int *)c)[val12] + ((int *)b)[val13];
    }
    if (j < 8) {
        val6 = j + 2;
    }
    if (j < 8 && val6 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 10, &alloc_db12f52e76e1ed1de1888d8f2930e7d2);
    }
    if (j < 8 && val6 < 10) {
        val15 = j + 2;
    }
    if (j < 8 && val6 < 10 && val15 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val15, 10, &alloc_ec251e6e9e3d4b5217a50909784c206c);
    }
    if (j < 8 && val6 < 10 && val15 < 10) {
        ((int *)a)[val15] = ((int *)a)[val6] + 1;
        val16 = j + 1;
    }
    if (j < 8 && val16 >= 10 && val6 < 10 && val15 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val16, 10, &alloc_766a4c9f9e23a3f0dd51deedf37338f9);
    }
    if (j < 8 && val6 < 10 && val16 < 10 && val15 < 10) {
        val17 = j + 1;
    }
    if (j < 8 && val17 >= 10 && val6 < 10 && val16 < 10 && val15 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val17, 10, &alloc_e313e970cfca129ca94ef13478605fc9);
    }
    if (j < 8 && val17 < 10 && val6 < 10 && val16 < 10 && val15 < 10) {
        val18 = j + 1;
    }
    if (j < 8 && val17 < 10 && val6 < 10 && val16 < 10 && val18 >= 10 && val15 < 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val18, 10, &alloc_5d845e4e0de1190429dcd79195dce759);
    }
    if (j < 8 && val18 < 10 && val17 < 10 && val6 < 10 && val16 < 10 && val15 < 10) {
        ((int *)b)[val18] = ((int *)b)[val16] + ((int *)a)[val17];
        val19 = j;
    }
    if (j < 8 && val18 < 10 && val17 < 10 && val6 < 10 && val16 < 10 && val15 < 10 && val19 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val19, 10, &alloc_e1120f63616a4cbe1cc40a35154b985c);
    }
    if (j < 8 && val18 < 10 && val17 < 10 && val19 < 10 && val6 < 10 && val16 < 10 && val15 < 10) {
        val20 = j;
    }
    if (j < 8 && val18 < 10 && val17 < 10 && val19 < 10 && val6 < 10 && val16 < 10 && val15 < 10 && val20 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val20, 10, &alloc_fba6e8274804213f943b7ccf90b8ceb2);
    }
    if (j < 8 && val18 < 10 && val17 < 10 && val19 < 10 && val6 < 10 && val20 < 10 && val16 < 10 && val15 < 10) {
        val21 = j;
    }
    if (j < 8 && val18 < 10 && val17 < 10 && val19 < 10 && val6 < 10 && val20 < 10 && val16 < 10 && val15 < 10 && val21 >= 10) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val21, 10, &alloc_ae481aa1a29de9b4ef6d1001a2008896);
    }
    if (j < 8 && val18 < 10 && val21 < 10 && val17 < 10 && val19 < 10 && val6 < 10 && val20 < 10 && val16 < 10 && val15 < 10) {
        ((int *)c)[val21] = ((int *)c)[val19] + ((int *)b)[val20];
        j = j + 1;
    }
}
