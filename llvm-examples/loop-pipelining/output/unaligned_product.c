void main(int l_a[10], int l_b[10], int l_c[10], void* r_a, void* r_b, void* r_c) {
  int l_i = 0;
  while (l_i < 10) {
    l_a[l_i] = (l_a[l_i] + 1);
    l_b[l_i] = (l_b[l_i] + l_a[l_i]);
    l_c[l_i] = (l_c[l_i] + l_b[l_i]);
    l_i = (l_i + 1);
  }
  char r_n[8];
  char r_c_var1[8];
  char r_b_var2[8];
  char r_a_var3[8];
  char r_j[8];
  long r_val5;
  long r_val6;
  long r_val7;
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
  long r_val18;
  long r_val19;
  long r_val20;
  long r_val21;
  (*((void**)(&r_a_var3))) = r_a;
  (*((void**)(&r_b_var2))) = r_b;
  (*((void**)(&r_c_var1))) = r_c;
  (*((unsigned long*)(&r_n))) = 10;
  (*((unsigned long*)(&r_j))) = 0;
  (*((unsigned int*)r_a)) = ((*((unsigned int*)r_a)) + 1);
  (*((unsigned int*)r_b)) = ((*((unsigned int*)r_b)) + (*((unsigned int*)r_a)));
  ((unsigned int*)r_a)[1] = (((unsigned int*)r_a)[1] + 1);
  if ((*((unsigned long*)(&r_j))) >= 8) {
    r_val5 = (*((unsigned long*)(&r_j)));
  }
  if (((*((unsigned long*)(&r_j))) >= 8) && (r_val5 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val5, 10, &r_alloc_2eb431f63ae4896b066f944852c62b63);
  }
  if (((*((unsigned long*)(&r_j))) >= 8) && (r_val5 < 10)) {
    r_val7 = (*((unsigned long*)(&r_j)));
  }
  if ((((*((unsigned long*)(&r_j))) >= 8) && (r_val5 < 10)) && (r_val7 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val7, 10, &r_alloc_bb008af1a11188dbc0a8220f06190d73);
  }
  if ((((*((unsigned long*)(&r_j))) >= 8) && (r_val5 < 10)) && (r_val7 < 10)) {
    r_val8 = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_j))) >= 8) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val8, 10, &r_alloc_bae3feef6ab792f9dddd1f61e8a2ced1);
  }
  if (((((*((unsigned long*)(&r_j))) >= 8) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) {
    ((unsigned int*)r_c)[r_val8] = (((unsigned int*)r_c)[r_val5] + ((unsigned int*)r_b)[r_val7]);
    r_val9 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if ((((((*((unsigned long*)(&r_j))) >= 8) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val9 >= 10)) && (r_val8 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val9, 10, &r_alloc_44014d371c28a91d445bc935d397da88);
  }
  if ((((((*((unsigned long*)(&r_j))) >= 8) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) {
    r_val10 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if (((((((*((unsigned long*)(&r_j))) >= 8) && (r_val10 >= 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val10, 10, &r_alloc_d6acdfa81a08d929191080bb8281517a);
  }
  if (((((((*((unsigned long*)(&r_j))) >= 8) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val10 < 10)) {
    r_val11 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if ((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val11 >= 10)) && (r_val8 < 10)) && (r_val10 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val11, 10, &r_alloc_e8ea127106c26cc7ad8e0642c4b2c171);
  }
  if ((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val11 < 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val10 < 10)) {
    ((unsigned int*)r_b)[r_val11] = (((unsigned int*)r_b)[r_val9] + ((unsigned int*)r_a)[r_val10]);
    r_val12 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if (((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val11 < 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val10 < 10)) && (r_val12 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val12, 10, &r_alloc_09ab0c4698002ff1be2861a2d737e0f9);
  }
  if (((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val11 < 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val12 < 10)) && (r_val10 < 10)) {
    r_val13 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if ((((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val11 < 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val13 >= 10)) && (r_val12 < 10)) && (r_val10 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val13, 10, &r_alloc_a99a5d4cc55dcc51ad4c685788710a5b);
  }
  if ((((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val11 < 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val12 < 10)) && (r_val10 < 10)) && (r_val13 < 10)) {
    r_val14 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if (((((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val11 < 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val14 >= 10)) && (r_val12 < 10)) && (r_val10 < 10)) && (r_val13 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val14, 10, &r_alloc_68b2bf2a0742d809e57390f761e71dad);
  }
  if (((((((((((*((unsigned long*)(&r_j))) >= 8) && (r_val11 < 10)) && (r_val9 < 10)) && (r_val5 < 10)) && (r_val7 < 10)) && (r_val8 < 10)) && (r_val12 < 10)) && (r_val10 < 10)) && (r_val13 < 10)) && (r_val14 < 10)) {
    ((unsigned int*)r_c)[r_val14] = (((unsigned int*)r_c)[r_val12] + ((unsigned int*)r_b)[r_val13]);
  }
  if ((*((unsigned long*)(&r_j))) < 8) {
    r_val6 = ((*((unsigned long*)(&r_j))) + 2);
  }
  if (((*((unsigned long*)(&r_j))) < 8) && (r_val6 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 10, &r_alloc_db12f52e76e1ed1de1888d8f2930e7d2);
  }
  if (((*((unsigned long*)(&r_j))) < 8) && (r_val6 < 10)) {
    r_val15 = ((*((unsigned long*)(&r_j))) + 2);
  }
  if ((((*((unsigned long*)(&r_j))) < 8) && (r_val15 >= 10)) && (r_val6 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val15, 10, &r_alloc_ec251e6e9e3d4b5217a50909784c206c);
  }
  if ((((*((unsigned long*)(&r_j))) < 8) && (r_val6 < 10)) && (r_val15 < 10)) {
    ((unsigned int*)r_a)[r_val15] = (((unsigned int*)r_a)[r_val6] + 1);
    r_val16 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if (((((*((unsigned long*)(&r_j))) < 8) && (r_val6 < 10)) && (r_val15 < 10)) && (r_val16 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val16, 10, &r_alloc_766a4c9f9e23a3f0dd51deedf37338f9);
  }
  if (((((*((unsigned long*)(&r_j))) < 8) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val15 < 10)) {
    r_val17 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if ((((((*((unsigned long*)(&r_j))) < 8) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val15 < 10)) && (r_val17 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val17, 10, &r_alloc_e313e970cfca129ca94ef13478605fc9);
  }
  if ((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val15 < 10)) {
    r_val18 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if (((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val18 >= 10)) && (r_val15 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val18, 10, &r_alloc_5d845e4e0de1190429dcd79195dce759);
  }
  if (((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val15 < 10)) && (r_val18 < 10)) {
    ((unsigned int*)r_b)[r_val18] = (((unsigned int*)r_b)[r_val16] + ((unsigned int*)r_a)[r_val17]);
    r_val19 = (*((unsigned long*)(&r_j)));
  }
  if ((((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val15 < 10)) && (r_val18 < 10)) && (r_val19 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val19, 10, &r_alloc_e1120f63616a4cbe1cc40a35154b985c);
  }
  if ((((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val19 < 10)) && (r_val15 < 10)) && (r_val18 < 10)) {
    r_val20 = (*((unsigned long*)(&r_j)));
  }
  if (((((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val19 < 10)) && (r_val15 < 10)) && (r_val18 < 10)) && (r_val20 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val20, 10, &r_alloc_fba6e8274804213f943b7ccf90b8ceb2);
  }
  if (((((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val19 < 10)) && (r_val15 < 10)) && (r_val18 < 10)) && (r_val20 < 10)) {
    r_val21 = (*((unsigned long*)(&r_j)));
  }
  if ((((((((((*((unsigned long*)(&r_j))) < 8) && (r_val21 >= 10)) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val19 < 10)) && (r_val15 < 10)) && (r_val18 < 10)) && (r_val20 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val21, 10, &r_alloc_ae481aa1a29de9b4ef6d1001a2008896);
  }
  if ((((((((((*((unsigned long*)(&r_j))) < 8) && (r_val17 < 10)) && (r_val6 < 10)) && (r_val16 < 10)) && (r_val19 < 10)) && (r_val15 < 10)) && (r_val18 < 10)) && (r_val21 < 10)) && (r_val20 < 10)) {
    ((unsigned int*)r_c)[r_val21] = (((unsigned int*)r_c)[r_val19] + ((unsigned int*)r_b)[r_val20]);
    (*((unsigned long*)(&r_j))) = ((*((unsigned long*)(&r_j))) + 1);
  }
}