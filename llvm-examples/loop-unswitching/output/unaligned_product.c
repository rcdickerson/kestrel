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
  long r_val9;
  long r_val10;
  long r_val11;
  long r_val12;
  long r_val13;
  long r_val14;
  long r_val15;
  long r_val16;
  long r_val17;
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
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val8, 10, &r_alloc_419ef0d9175c3c3d25b6349e67ee0cbd);
  }
  if (((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) {
    r_val9 = (*((unsigned long*)(&r_j)));
  }
  if ((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) && (r_val9 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val9, 10, &r_alloc_d2d5579a465f4b0e260596020158df10);
  }
  if ((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) && (r_val9 < 10)) {
    ((unsigned int*)r_a)[r_val9] = (((unsigned int*)r_a)[r_val8] + r_k);
    r_val10 = ((*((unsigned long*)(&r_j))) - 1);
  }
  if (((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val10 >= 10)) && (r_val8 < 10)) && (r_val9 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val10, 10, &r_alloc_e3f13fad5a0fb42e992397669711c193);
  }
  if (((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) && (r_val9 < 10)) && (r_val10 < 10)) {
    r_val11 = ((*((unsigned long*)(&r_j))) - 1);
  }
  if ((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val8 < 10)) && (r_val9 < 10)) && (r_val10 < 10)) && (r_val11 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val11, 10, &r_alloc_bb2f62fcbec2afd6481e273b7e37fcc1);
  }
  if ((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val11 < 10)) && (r_val8 < 10)) && (r_val9 < 10)) && (r_val10 < 10)) {
    r_val12 = (*((unsigned long*)(&r_j)));
  }
  if (((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val11 < 10)) && (r_val8 < 10)) && (r_val9 < 10)) && (r_val10 < 10)) && (r_val12 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val12, 10, &r_alloc_31ffd0f23462b2f4117f2c5301d8027b);
  }
  if (((((((((int)r_x) >= 7) && ((*((unsigned long*)(&r_j))) < 10)) && (r_val11 < 10)) && (r_val12 < 10)) && (r_val8 < 10)) && (r_val9 < 10)) && (r_val10 < 10)) {
    ((unsigned int*)r_b)[r_val12] = (((unsigned int*)r_a)[r_val10] * ((unsigned int*)r_b)[r_val11]);
    (*((unsigned long*)(&r_j))) = ((*((unsigned long*)(&r_j))) + 1);
  }
  if (((int)r_x) < 7) {
    (*((unsigned long*)(&r_j_var7))) = 0;
  }
  if (!((((int)r_x) < 7) ? ((*((unsigned long*)(&r_j_var7))) < 10) : ((*((unsigned long*)(&r_j))) < 10))) {
  }
  if ((((int)r_x) < 7) && ((*((unsigned long*)(&r_j_var7))) < 10)) {
    r_val13 = (*((unsigned long*)(&r_j_var7)));
  }
  if (((((int)r_x) < 7) && (r_val13 >= 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val13, 10, &r_alloc_a431e0af1f0a773d7894a8f7648fcbbb);
  }
  if (((((int)r_x) < 7) && (r_val13 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) {
    r_val14 = (*((unsigned long*)(&r_j_var7)));
  }
  if ((((((int)r_x) < 7) && (r_val13 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val14 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val14, 10, &r_alloc_86a95f0408d87e2b4012bd6715ad108d);
  }
  if ((((((int)r_x) < 7) && (r_val13 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val14 < 10)) {
    ((unsigned int*)r_a)[r_val14] = (((unsigned int*)r_a)[r_val13] + r_k);
    r_val15 = (*((unsigned long*)(&r_j_var7)));
  }
  if (((((((int)r_x) < 7) && (r_val13 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val15 >= 10)) && (r_val14 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val15, 10, &r_alloc_72db5233068273f5dabaebf836ed1389);
  }
  if (((((((int)r_x) < 7) && (r_val13 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val15 < 10)) && (r_val14 < 10)) {
    r_val16 = (*((unsigned long*)(&r_j_var7)));
  }
  if ((((((((int)r_x) < 7) && (r_val13 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val15 < 10)) && (r_val16 >= 10)) && (r_val14 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val16, 10, &r_alloc_40b9f4e097b3d8001419ebb57560c155);
  }
  if ((((((((int)r_x) < 7) && (r_val13 < 10)) && (r_val16 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val15 < 10)) && (r_val14 < 10)) {
    r_val17 = (*((unsigned long*)(&r_j_var7)));
  }
  if (((((((((int)r_x) < 7) && (r_val13 < 10)) && (r_val16 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val15 < 10)) && (r_val17 >= 10)) && (r_val14 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val17, 10, &r_alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2);
  }
  if (((((((((int)r_x) < 7) && (r_val13 < 10)) && (r_val16 < 10)) && ((*((unsigned long*)(&r_j_var7))) < 10)) && (r_val15 < 10)) && (r_val17 < 10)) && (r_val14 < 10)) {
    ((unsigned int*)r_b)[r_val17] = (((unsigned int*)r_a)[r_val15] * ((unsigned int*)r_c)[r_val16]);
    (*((unsigned long*)(&r_j_var7))) = ((*((unsigned long*)(&r_j_var7))) + 1);
  }
}