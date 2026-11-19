void main(int l_A[A_SIZE], int l_val, void* r_a, int r_val) {
  int l_i = 0;
  while ((l_i < A_SIZE) && (l_A[l_i] < l_val)) {
    l_i = (l_i + 1);
  }
  int l_len = (A_SIZE + 1);
  l_A[l_i] = l_val;
  while (l_i < l_len) {
    l_i = (l_i + 1);
  }
  char r_len[8];
  char r_a_size[8];
  char r_val_var2[4];
  char r_a_var3[8];
  char r_j[8];
  long r_val5;
  long r_val6;
  long r_val7;
  long r_val8;
  long r_val9;
  long r_val10;
  (*((void**)(&r_a_var3))) = r_a;
  (*((unsigned int*)(&r_val_var2))) = r_val;
  (*((unsigned long*)(&r_a_size))) = 10;
  (*((unsigned long*)(&r_j))) = 0;
  if ((*((unsigned long*)(&r_j))) < 10) {
    r_val6 = (*((unsigned long*)(&r_j)));
  }
  if (((*((unsigned long*)(&r_j))) < 10) && (r_val6 >= 11)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 11, &alloc_1b6aad345a552ecadc4ef2f80a0f897d);
  }
  if (((*((unsigned long*)(&r_j))) >= 10) || (!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10)))) {
    (*((unsigned long*)(&r_len))) = 11;
    r_val5 = (*((unsigned long*)(&r_j)));
  }
  if ((r_val5 >= 11) && (((*((unsigned long*)(&r_j))) >= 10) || (!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10))))) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val5, 11, &alloc_a74a36876f5d89ac1dedf5b0e55c3dda);
  }
  if ((((*((unsigned long*)(&r_j))) >= 10) || (!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10)))) && (r_val5 < 11)) {
    ((unsigned int*)r_a)[r_val5] = r_val;
  }
  if (((((*((unsigned long*)(&r_j))) >= 10) || (!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10)))) && (r_val5 < 11)) && ((*((unsigned long*)(&r_j))) >= 11)) {
  }
  if (((((*((unsigned long*)(&r_j))) >= 10) || (!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10)))) && (r_val5 < 11)) && ((*((unsigned long*)(&r_j))) < 11)) {
    r_val9 = (*((unsigned long*)(&r_j)));
    r_val10 = (r_val9 + 1);
  }
  if ((((((*((unsigned long*)(&r_j))) >= 10) || (!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10)))) && (r_val5 < 11)) && (r_val10 >= r_val9)) && ((*((unsigned long*)(&r_j))) < 11)) {
    (*((unsigned long*)(&r_j))) = r_val10;
  }
  if ((((r_val10 < r_val9) && (((*((unsigned long*)(&r_j))) >= 10) || (!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10))))) && (r_val5 < 11)) && ((*((unsigned long*)(&r_j))) < 11)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_6a05b4f1dc13a4b1e8be83728286bf0f);
  }
  if ((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) {
    r_val7 = (*((unsigned long*)(&r_j)));
    r_val8 = (r_val7 + 1);
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) && (r_val8 >= r_val7)) {
    (*((unsigned long*)(&r_j))) = r_val8;
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (r_val8 < r_val7)) && (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_c6a7a81a76189b99aa0755c4e24a8496);
  }
}