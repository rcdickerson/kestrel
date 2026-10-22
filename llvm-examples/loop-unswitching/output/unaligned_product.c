void main(int l_a[10], int l_b[10], int l_c[10], int l_k, int l_x, void* r_a, void* r_b, void* r_c, int r_k, int r_x) {
  int l_i = 0;
  while (l_i < 10) {
    l_a[l_i] = (l_a[l_i] + l_k);
    if (l_x < 7) {
      l_b[l_i] = (l_a[l_i] * l_c[l_i]);
    } else {
      l_b[l_i] = (l_a[l_i - 1] * l_b[l_i - 1]);
    }
    l_i = (l_i + 1);
  }
  char r_n[8];
  char r_x_var1[4];
  char r_k_var2[4];
  char r_c_var3[8];
  char r_b_var4[8];
  char r_a_var5[8];
  char r_j[8];
  char r_j_var7[8];
  long r_val8;
  struct literal_struct_0 r_call9;
  long r_val10;
  long r_val11;
  long r_val12;
  long r_val13;
  long r_val14;
  struct literal_struct_0 r_call15;
  long r_val16;
  long r_val17;
  long r_val18;
  long r_val19;
  struct literal_struct_0 r_call20;
  long r_val21;
  long r_val22;
  long r_val23;
  struct literal_struct_0 r_call24;
  long r_val25;
  long r_val26;
  long r_val27;
  (*((void**)(&r_a_var5))) = r_a;
  (*((void**)(&r_b_var4))) = r_b;
  (*((void**)(&r_c_var3))) = r_c;
  (*((unsigned int*)(&r_k_var2))) = r_k;
  (*((unsigned int*)(&r_x_var1))) = r_x;
  (*((unsigned long*)(&r_n))) = 10;
  if (((int)r_x) >= 7) {
    (*((unsigned long*)(&r_j))) = 0;
  }
  if ((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) {
    r_val8 = (*((unsigned long*)(&r_j)));
  }
  if (((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val8, 10, &alloc_419ef0d9175c3c3d25b6349e67ee0cbd);
  }
  if (((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) {
    r_call9 = llvm_sadd_with_overflow_i32(((unsigned int*)r_a)[r_val8], r_k);
  }
  if ((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) && (!r_call9.field1)) {
    r_val10 = (*((unsigned long*)(&r_j)));
  }
  if (((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) && (!r_call9.field1)) && (r_val10 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val10, 10, &alloc_d2d5579a465f4b0e260596020158df10);
  }
  if (((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val8 < 10)) && (!r_call9.field1)) {
    ((unsigned int*)r_a)[r_val10] = r_call9.field0;
    r_val11 = (*((unsigned long*)(&r_j)));
    r_val12 = (r_val11 - 1);
  }
  if (((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (r_val12 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val12, 10, &alloc_e3f13fad5a0fb42e992397669711c193);
  }
  if (((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (r_val12 < 10)) {
    r_val13 = (*((unsigned long*)(&r_j)));
    r_val14 = (r_val13 - 1);
  }
  if (((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (r_val12 < 10)) && (r_val14 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val14, 10, &alloc_bb2f62fcbec2afd6481e273b7e37fcc1);
  }
  if (((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (r_val12 < 10)) {
    r_call15 = llvm_smul_with_overflow_i32(((unsigned int*)r_a)[r_val12], ((unsigned int*)r_b)[r_val14]);
  }
  if ((((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (!r_call15.field1)) && (r_val12 < 10)) {
    r_val16 = (*((unsigned long*)(&r_j)));
  }
  if (((((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (!r_call15.field1)) && (r_val12 < 10)) && (r_val16 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val16, 10, &alloc_31ffd0f23462b2f4117f2c5301d8027b);
  }
  if (((((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (!r_call15.field1)) && (r_val12 < 10)) && (r_val16 < 10)) {
    ((unsigned int*)r_b)[r_val16] = r_call15.field0;
    r_val17 = (*((unsigned long*)(&r_j)));
    r_val18 = (r_val17 + 1);
  }
  if ((((((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (r_val18 >= r_val17)) && (!r_call15.field1)) && (r_val12 < 10)) && (r_val16 < 10)) {
    (*((unsigned long*)(&r_j))) = r_val18;
  }
  if ((((((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (!r_call15.field1)) && (r_val12 < 10)) && (r_val18 < r_val17)) && (r_val16 < 10)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_abbc3ba085879e0c58420fdd90df364b);
  }
  if ((((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && r_call15.field1) && (r_val12 < 10)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_e3f13fad5a0fb42e992397669711c193);
  }
  if ((((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val13 < 1)) && (r_val11 >= 1)) && (r_val8 < 10)) && (!r_call9.field1)) && (r_val12 < 10)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_a71056d669a165115308cd734a984c01);
  }
  if ((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 < 10)) && (r_val11 < 1)) && (r_val8 < 10)) && (!r_call9.field1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_3851e86263c4f1dc61060dfc24bfb5f8);
  }
  if ((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) && r_call9.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_419ef0d9175c3c3d25b6349e67ee0cbd);
  }
  if (((int)r_x) < 7) {
    (*((unsigned long*)(&r_j_var7))) = 0;
  }
  if (!((((int)r_x) < 7) ? ((*((unsigned long*)(&r_j_var7))) < 10) : ((*((unsigned long*)(&r_j))) < 10))) {
  }
  if ((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) {
    r_val19 = (*((unsigned long*)(&r_j_var7)));
  }
  if (((((int)r_x) < 7) && (r_val19 >= 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val19, 10, &alloc_a431e0af1f0a773d7894a8f7648fcbbb);
  }
  if (((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val19 < 10)) {
    r_call20 = llvm_sadd_with_overflow_i32(((unsigned int*)r_a)[r_val19], r_k);
  }
  if ((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val19 < 10)) {
    r_val21 = (*((unsigned long*)(&r_j_var7)));
  }
  if (((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 >= 10)) && (r_val19 < 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val21, 10, &alloc_86a95f0408d87e2b4012bd6715ad108d);
  }
  if (((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) {
    ((unsigned int*)r_a)[r_val21] = r_call20.field0;
    r_val22 = (*((unsigned long*)(&r_j_var7)));
  }
  if ((((((((int)r_x) < 7) && (r_val22 >= 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val22, 10, &alloc_72db5233068273f5dabaebf836ed1389);
  }
  if ((((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) {
    r_val23 = (*((unsigned long*)(&r_j_var7)));
  }
  if (((((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val23 >= 10)) && (r_val22 < 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val23, 10, &alloc_40b9f4e097b3d8001419ebb57560c155);
  }
  if (((((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) && (r_val23 < 10)) {
    r_call24 = llvm_smul_with_overflow_i32(((unsigned int*)r_a)[r_val22], ((unsigned int*)r_c)[r_val23]);
  }
  if ((((((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) && (r_val23 < 10)) && (!r_call24.field1)) {
    r_val25 = (*((unsigned long*)(&r_j_var7)));
  }
  if (((((((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) && (r_val23 < 10)) && (!r_call24.field1)) && (r_val25 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val25, 10, &alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2);
  }
  if (((((((((((int)r_x) < 7) && (r_val25 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) && (r_val23 < 10)) && (!r_call24.field1)) {
    ((unsigned int*)r_b)[r_val25] = r_call24.field0;
    r_val26 = (*((unsigned long*)(&r_j_var7)));
    r_val27 = (r_val26 + 1);
  }
  if ((((((((((((int)r_x) < 7) && (r_val25 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val27 >= r_val26)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) && (r_val23 < 10)) && (!r_call24.field1)) {
    (*((unsigned long*)(&r_j_var7))) = r_val27;
  }
  if ((((((((((((int)r_x) < 7) && (r_val25 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val27 < r_val26)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) && (r_val23 < 10)) && (!r_call24.field1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_9a0d9beb0fd0d5747443c939bdea398d);
  }
  if ((((((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (!r_call20.field1)) && (r_val21 < 10)) && (r_val19 < 10)) && (r_val22 < 10)) && (r_val23 < 10)) && r_call24.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_72db5233068273f5dabaebf836ed1389);
  }
  if ((((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val19 < 10)) && r_call20.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_a431e0af1f0a773d7894a8f7648fcbbb);
  }
}