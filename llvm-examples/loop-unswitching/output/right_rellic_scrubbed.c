struct literal_struct_0 llvm_smul_with_overflow_i64(long arg0, long arg1);
void _RNvNtCscI6d9CVNmLh_4core10intrinsics9cold_pathCs7Hul5VkTjfJ_5right(void) {
}
void _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(void *this, long count, long size, void *arg3) {
    int self;
    int overflow;
    int self_var2;
    int rhs;
    int b;
    int rhs_var5;
    int size_var6;
    int self_var7;
    int self_var8;
    struct literal_struct_0 call9;
    long val10;
    char val11;
    long val12;
    char val13;
    self_var8 = this;
    self_var7 = count;
    size_var6 = size;
    rhs_var5 = size;
    call9 = llvm_smul_with_overflow_i64(count, size);
    val10 = call9.field0;
    val11 = call9.field1;
    b = val11;
    rhs = val10;
    if (!val11) {
        val12 = this;
        self_var2 = val12;
        val13 = val12 + val10 < val12 ^ val10 < 0L;
        overflow = val13;
    }
    if (!val11 && val13 ^ 1) {
    } else {
        self = &alloc_0ed0763d8bf93ac79247e07858374e35;
        _RNvNtCscI6d9CVNmLh_4core9panicking18panic_nounwind_fmt(&alloc_0ed0763d8bf93ac79247e07858374e35, 421, 0, arg3);
    }
}
void right(void *a, void *b, void *c, int k, int x) {
    int count;
    int self;
    int count_var2;
    int self_var3;
    int count_var4;
    int self_var5;
    int count_var6;
    int self_var7;
    int count_var8;
    int self_var9;
    int count_var10;
    int self_var11;
    int count_var12;
    int self_var13;
    int count_var14;
    int self_var15;
    int count_var16;
    int self_var17;
    int count_var18;
    int self_var19;
    int n;
    int x_var21;
    int k_var22;
    int c_var23;
    int b_var24;
    int a_var25;
    int j;
    int j_var27;
    long val28;
    void *val29;
    long val30;
    long val31;
    void *val32;
    long val33;
    long val34;
    void *val35;
    long val36;
    long val37;
    void *val38;
    long val39;
    long val40;
    void *val41;
    long val42;
    long val43;
    void *val44;
    long val45;
    long val46;
    void *val47;
    long val48;
    long val49;
    void *val50;
    long val51;
    long val52;
    void *val53;
    long val54;
    long val55;
    void *val56;
    long val57;
    a_var25 = a;
    b_var24 = b;
    c_var23 = c;
    k_var22 = k;
    x_var21 = x;
    n = 10;
    if (x >= 7) {
        j = 0;
    }
    if ((j) < 10 && x >= 7) {
        val28 = (j);
        self = a;
        count = val28;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(a, val28, 4, &alloc_fc6e52086a0304bf109d11264a2bf9ec);
        val29 = &((int *)a)[val28];
        val30 = val29;
    }
    if ((j) < 10 && x >= 7 && (val30 & 3) != 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val30, &alloc_970eef56f9d83005df8375449746a3c8);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && !((val29 == 0 && 1) ^ 1)) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_970eef56f9d83005df8375449746a3c8);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1) {
        val31 = (j);
        self_var3 = a;
        count_var2 = val31;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(a, val31, 4, &alloc_8008df1f4e02f7aae2c1daa0775ed744);
        val32 = &((int *)a)[val31];
        val33 = val32;
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val33 & 3) != 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val33, &alloc_d2d5579a465f4b0e260596020158df10);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && !((val32 == 0 && 1) ^ 1) && (val33 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_d2d5579a465f4b0e260596020158df10);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1) {
        *(int *)val32 = *(int *)val29 + k;
        val34 = (j - 1);
        self_var5 = a;
        count_var4 = val34;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(a, val34, 4, &alloc_125529c3e3a86ef842e3bcb4e56fc8c4);
        val35 = &((int *)a)[val34];
        val36 = val35;
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && (val36 & 3) != 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val36, &alloc_d43d41868e27e86fdfa80ed5db808a93);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && !((val35 == 0 && 1) ^ 1) && (val36 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_d43d41868e27e86fdfa80ed5db808a93);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val35 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && (val36 & 3) == 0) {
        val37 = (j - 1);
        self_var7 = b;
        count_var6 = val37;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(b, val37, 4, &alloc_505b6a3c86ac0845f2ebe6fbadebb444);
        val38 = &((int *)b)[val37];
        val39 = val38;
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val35 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && (val39 & 3) != 0 && (val36 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val39, &alloc_50a66c3f3e41f7b4c64af7a47a9ccab1);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val35 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && !((val38 == 0 && 1) ^ 1) && (val39 & 3) == 0 && (val36 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_50a66c3f3e41f7b4c64af7a47a9ccab1);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val35 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && (val39 & 3) == 0 && (val38 == 0 && 1) ^ 1 && (val36 & 3) == 0) {
        val40 = (j);
        self_var9 = b;
        count_var8 = val40;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(b, val40, 4, &alloc_f6eb710abe499e857fd0b2d658839bf6);
        val41 = &((int *)b)[val40];
        val42 = val41;
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val35 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && (val39 & 3) == 0 && (val38 == 0 && 1) ^ 1 && (val36 & 3) == 0 && (val42 & 3) != 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val42, &alloc_31ffd0f23462b2f4117f2c5301d8027b);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val35 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && (val42 & 3) == 0 && (val39 & 3) == 0 && (val38 == 0 && 1) ^ 1 && (val36 & 3) == 0 && !((val41 == 0 && 1) ^ 1)) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_31ffd0f23462b2f4117f2c5301d8027b);
    }
    if ((j) < 10 && (val30 & 3) == 0 && x >= 7 && (val29 == 0 && 1) ^ 1 && (val35 == 0 && 1) ^ 1 && (val33 & 3) == 0 && (val32 == 0 && 1) ^ 1 && (val42 & 3) == 0 && (val39 & 3) == 0 && (val38 == 0 && 1) ^ 1 && (val36 & 3) == 0 && (val41 == 0 && 1) ^ 1) {
        *(int *)val41 = *(int *)val35 * *(int *)val38;
        j = j + 1;
    }
    if (x < 7) {
        j_var27 = 0;
    }
    if (!(x < 7 ? (j_var27) < 10 : (j) < 10)) {
    }
    if (x < 7 && (j_var27) < 10) {
        val43 = (j_var27);
        self_var11 = a;
        count_var10 = val43;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(a, val43, 4, &alloc_9112371d34dce514bcd7d34762d86f28);
        val44 = &((int *)a)[val43];
        val45 = val44;
    }
    if (x < 7 && (j_var27) < 10 && (val45 & 3) != 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val45, &alloc_0041c665341a6cb1f758da048db60ac0);
    }
    if (!((val44 == 0 && 1) ^ 1) && x < 7 && (j_var27) < 10 && (val45 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_0041c665341a6cb1f758da048db60ac0);
    }
    if (x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0) {
        val46 = (j_var27);
        self_var13 = a;
        count_var12 = val46;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(a, val46, 4, &alloc_3324106411bf04d9d78e5cc9ddc5ecde);
        val47 = &((int *)a)[val46];
        val48 = val47;
    }
    if ((val48 & 3) != 0 && x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val48, &alloc_86a95f0408d87e2b4012bd6715ad108d);
    }
    if (!((val47 == 0 && 1) ^ 1) && x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0 && (val48 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_86a95f0408d87e2b4012bd6715ad108d);
    }
    if (x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0) {
        *(int *)val47 = *(int *)val44 + k;
        val49 = (j_var27);
        self_var15 = a;
        count_var14 = val49;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(a, val49, 4, &alloc_f8ad5f429a93b792719cdfee15997438);
        val50 = &((int *)a)[val49];
        val51 = val50;
    }
    if (x < 7 && (val51 & 3) != 0 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val51, &alloc_13cbad28ad8f055f3ad8a2fac4d94e9b);
    }
    if (x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0 && (val51 & 3) == 0 && !((val50 == 0 && 1) ^ 1)) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_13cbad28ad8f055f3ad8a2fac4d94e9b);
    }
    if (x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0 && (val51 & 3) == 0 && (val50 == 0 && 1) ^ 1) {
        val52 = (j_var27);
        self_var17 = c;
        count_var16 = val52;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(c, val52, 4, &alloc_15920ab35f5e2ecbeb736a6a269f18e1);
        val53 = &((int *)c)[val52];
        val54 = val53;
    }
    if (x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val54 & 3) != 0 && (val48 & 3) == 0 && (val51 & 3) == 0 && (val50 == 0 && 1) ^ 1) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val54, &alloc_0475a419af21785faa84cfc43594c5e4);
    }
    if (x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val54 & 3) == 0 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0 && !((val53 == 0 && 1) ^ 1) && (val51 & 3) == 0 && (val50 == 0 && 1) ^ 1) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_0475a419af21785faa84cfc43594c5e4);
    }
    if (x < 7 && (j_var27) < 10 && (val44 == 0 && 1) ^ 1 && (val54 & 3) == 0 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0 && (val51 & 3) == 0 && (val50 == 0 && 1) ^ 1 && (val53 == 0 && 1) ^ 1) {
        val55 = (j_var27);
        self_var19 = b;
        count_var18 = val55;
        _RNvNvMNtNtCscI6d9CVNmLh_4core3ptr7mut_ptrOp6offset18precondition_checkCs7Hul5VkTjfJ_5right(b, val55, 4, &alloc_40399a33516c6026f412df314381bd9d);
        val56 = &((int *)b)[val55];
        val57 = val56;
    }
    if (x < 7 && (j_var27) < 10 && (val57 & 3) != 0 && (val44 == 0 && 1) ^ 1 && (val54 & 3) == 0 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0 && (val51 & 3) == 0 && (val50 == 0 && 1) ^ 1 && (val53 == 0 && 1) ^ 1) {
        _RNvNtCscI6d9CVNmLh_4core9panicking36panic_misaligned_pointer_dereference(4, val57, &alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2);
    }
    if (x < 7 && (j_var27) < 10 && (val57 & 3) == 0 && (val44 == 0 && 1) ^ 1 && (val54 & 3) == 0 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0 && (val51 & 3) == 0 && (val50 == 0 && 1) ^ 1 && (val53 == 0 && 1) ^ 1 && !((val56 == 0 && 1) ^ 1)) {
        _RNvNtCscI6d9CVNmLh_4core9panicking30panic_null_pointer_dereference(&alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2);
    }
    if ((val56 == 0 && 1) ^ 1 && x < 7 && (j_var27) < 10 && (val57 & 3) == 0 && (val44 == 0 && 1) ^ 1 && (val54 & 3) == 0 && (val45 & 3) == 0 && (val47 == 0 && 1) ^ 1 && (val48 & 3) == 0 && (val51 & 3) == 0 && (val50 == 0 && 1) ^ 1 && (val53 == 0 && 1) ^ 1) {
        *(int *)val56 = *(int *)val50 * *(int *)val53;
        j_var27 = j_var27 + 1;
    }
}
