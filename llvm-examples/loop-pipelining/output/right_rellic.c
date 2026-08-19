void right(void *a, void *b, void *c);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(unsigned long arg0, unsigned long arg1, void *arg2);
char alloc_fcdcb07e6e3c3b03db85f8b11c83aa91[39] = "llvm-examples/loop-pipelining/right.rs\000";
struct literal_struct_0 {
    void *field0;
    char field1[16];
};
struct literal_struct_0 alloc_2eb431f63ae4896b066f944852c62b63 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\021\000\000\000\f\000\000\000"};
struct literal_struct_0 alloc_bb008af1a11188dbc0a8220f06190d73 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\021\000\000\000\023\000\000\000"};
struct literal_struct_0 alloc_bae3feef6ab792f9dddd1f61e8a2ced1 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\021\000\000\000\005\000\000\000"};
struct literal_struct_0 alloc_44014d371c28a91d445bc935d397da88 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\022\000\000\000\020\000\000\000"};
struct literal_struct_0 alloc_d6acdfa81a08d929191080bb8281517a = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\022\000\000\000\033\000\000\000"};
struct literal_struct_0 alloc_e8ea127106c26cc7ad8e0642c4b2c171 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\022\000\000\000\005\000\000\000"};
struct literal_struct_0 alloc_09ab0c4698002ff1be2861a2d737e0f9 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\023\000\000\000\020\000\000\000"};
struct literal_struct_0 alloc_a99a5d4cc55dcc51ad4c685788710a5b = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\023\000\000\000\033\000\000\000"};
struct literal_struct_0 alloc_68b2bf2a0742d809e57390f761e71dad = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\023\000\000\000\005\000\000\000"};
struct literal_struct_0 alloc_db12f52e76e1ed1de1888d8f2930e7d2 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\v\000\000\000\024\000\000\000"};
struct literal_struct_0 alloc_ec251e6e9e3d4b5217a50909784c206c = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\v\000\000\000\t\000\000\000"};
struct literal_struct_0 alloc_766a4c9f9e23a3f0dd51deedf37338f9 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\f\000\000\000\024\000\000\000"};
struct literal_struct_0 alloc_e313e970cfca129ca94ef13478605fc9 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\f\000\000\000\037\000\000\000"};
struct literal_struct_0 alloc_5d845e4e0de1190429dcd79195dce759 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\f\000\000\000\t\000\000\000"};
struct literal_struct_0 alloc_e1120f63616a4cbe1cc40a35154b985c = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\r\000\000\000\020\000\000\000"};
struct literal_struct_0 alloc_fba6e8274804213f943b7ccf90b8ceb2 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\r\000\000\000\027\000\000\000"};
struct literal_struct_0 alloc_ae481aa1a29de9b4ef6d1001a2008896 = {"llvm-examples/loop-pipelining/right.rs", "&\000\000\000\000\000\000\000\r\000\000\000\t\000\000\000"};
void right(void *a, void *b, void *c) {
    char n[8];
    char c_var1[8];
    char b_var2[8];
    char a_var3[8];
    char j[8];
    unsigned long val5;
    unsigned long val6;
    unsigned long val7;
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
    unsigned long val18;
    unsigned long val19;
    unsigned long val20;
    unsigned long val21;
    *(void **)(&a_var3) = a;
    *(void **)(&b_var2) = b;
    *(void **)(&c_var1) = c;
    *(unsigned long *)(&n) = 10UL;
    *(unsigned long *)(&j) = 0UL;
    *((unsigned int *)a) = *((unsigned int *)a) + 1U;
    *((unsigned int *)b) = *((unsigned int *)b) + *((unsigned int *)a);
    ((unsigned int *)a)[1UL] = ((unsigned int *)a)[1UL] + 1U;
    if (*(unsigned long *)(&j) >= 8UL) {
        val5 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) >= 8UL && val5 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val5, 10UL, &alloc_2eb431f63ae4896b066f944852c62b63);
    }
    if (*(unsigned long *)(&j) >= 8UL && val5 < 10UL) {
        val7 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) >= 8UL && val5 < 10UL && val7 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val7, 10UL, &alloc_bb008af1a11188dbc0a8220f06190d73);
    }
    if (*(unsigned long *)(&j) >= 8UL && val5 < 10UL && val7 < 10UL) {
        val8 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) >= 8UL && val5 < 10UL && val8 >= 10UL && val7 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val8, 10UL, &alloc_bae3feef6ab792f9dddd1f61e8a2ced1);
    }
    if (*(unsigned long *)(&j) >= 8UL && val5 < 10UL && val7 < 10UL && val8 < 10UL) {
        ((unsigned int *)c)[val8] = ((unsigned int *)c)[val5] + ((unsigned int *)b)[val7];
        val9 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 >= 10UL && val5 < 10UL && val7 < 10UL && val8 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val9, 10UL, &alloc_44014d371c28a91d445bc935d397da88);
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val7 < 10UL && val8 < 10UL) {
        val10 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 >= 10UL && val7 < 10UL && val8 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val10, 10UL, &alloc_d6acdfa81a08d929191080bb8281517a);
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val8 < 10UL) {
        val11 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val8 < 10UL && val11 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val11, 10UL, &alloc_e8ea127106c26cc7ad8e0642c4b2c171);
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val8 < 10UL && val11 < 10UL) {
        ((unsigned int *)b)[val11] = ((unsigned int *)b)[val9] + ((unsigned int *)a)[val10];
        val12 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) >= 8UL && val12 >= 10UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val8 < 10UL && val11 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val12, 10UL, &alloc_09ab0c4698002ff1be2861a2d737e0f9);
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val8 < 10UL && val12 < 10UL && val11 < 10UL) {
        val13 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val8 < 10UL && val12 < 10UL && val11 < 10UL && val13 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val13, 10UL, &alloc_a99a5d4cc55dcc51ad4c685788710a5b);
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val13 < 10UL && val8 < 10UL && val12 < 10UL && val11 < 10UL) {
        val14 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val10 < 10UL && val7 < 10UL && val13 < 10UL && val8 < 10UL && val12 < 10UL && val11 < 10UL && val14 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val14, 10UL, &alloc_68b2bf2a0742d809e57390f761e71dad);
    }
    if (*(unsigned long *)(&j) >= 8UL && val9 < 10UL && val5 < 10UL && val14 < 10UL && val10 < 10UL && val7 < 10UL && val13 < 10UL && val8 < 10UL && val12 < 10UL && val11 < 10UL) {
        ((unsigned int *)c)[val14] = ((unsigned int *)c)[val12] + ((unsigned int *)b)[val13];
        return;
    }
    if (*(unsigned long *)(&j) < 8UL) {
        val6 = *(unsigned long *)(&j) + 2UL;
    }
    if (*(unsigned long *)(&j) < 8UL && val6 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val6, 10UL, &alloc_db12f52e76e1ed1de1888d8f2930e7d2);
    }
    if (*(unsigned long *)(&j) < 8UL && val6 < 10UL) {
        val15 = *(unsigned long *)(&j) + 2UL;
    }
    if (*(unsigned long *)(&j) < 8UL && val15 >= 10UL && val6 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val15, 10UL, &alloc_ec251e6e9e3d4b5217a50909784c206c);
    }
    if (*(unsigned long *)(&j) < 8UL && val6 < 10UL && val15 < 10UL) {
        ((unsigned int *)a)[val15] = ((unsigned int *)a)[val6] + 1U;
        val16 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) < 8UL && val16 >= 10UL && val6 < 10UL && val15 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val16, 10UL, &alloc_766a4c9f9e23a3f0dd51deedf37338f9);
    }
    if (*(unsigned long *)(&j) < 8UL && val16 < 10UL && val6 < 10UL && val15 < 10UL) {
        val17 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) < 8UL && val16 < 10UL && val6 < 10UL && val17 >= 10UL && val15 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val17, 10UL, &alloc_e313e970cfca129ca94ef13478605fc9);
    }
    if (*(unsigned long *)(&j) < 8UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL) {
        val18 = *(unsigned long *)(&j) + 1UL;
    }
    if (*(unsigned long *)(&j) < 8UL && val18 >= 10UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val18, 10UL, &alloc_5d845e4e0de1190429dcd79195dce759);
    }
    if (*(unsigned long *)(&j) < 8UL && val18 < 10UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL) {
        ((unsigned int *)b)[val18] = ((unsigned int *)b)[val16] + ((unsigned int *)a)[val17];
        val19 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 8UL && val18 < 10UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL && val19 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val19, 10UL, &alloc_e1120f63616a4cbe1cc40a35154b985c);
    }
    if (*(unsigned long *)(&j) < 8UL && val19 < 10UL && val18 < 10UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL) {
        val20 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 8UL && val19 < 10UL && val18 < 10UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL && val20 >= 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val20, 10UL, &alloc_fba6e8274804213f943b7ccf90b8ceb2);
    }
    if (*(unsigned long *)(&j) < 8UL && val19 < 10UL && val18 < 10UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL && val20 < 10UL) {
        val21 = *(unsigned long *)(&j);
    }
    if (*(unsigned long *)(&j) < 8UL && val19 < 10UL && val18 < 10UL && val16 < 10UL && val6 < 10UL && val21 >= 10UL && val15 < 10UL && val17 < 10UL && val20 < 10UL) {
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(val21, 10UL, &alloc_ae481aa1a29de9b4ef6d1001a2008896);
    }
    if (*(unsigned long *)(&j) < 8UL && val19 < 10UL && val18 < 10UL && val16 < 10UL && val6 < 10UL && val15 < 10UL && val17 < 10UL && val20 < 10UL && val21 < 10UL) {
        ((unsigned int *)c)[val21] = ((unsigned int *)c)[val19] + ((unsigned int *)b)[val20];
        *(unsigned long *)(&j) = *(unsigned long *)(&j) + 1UL;
    }
}
