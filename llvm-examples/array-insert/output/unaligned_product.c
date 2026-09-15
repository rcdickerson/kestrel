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
  (*((void**)(&r_a_var3))) = r_a;
  (*((unsigned int*)(&r_val_var2))) = r_val;
  (*((unsigned long*)(&r_a_size))) = 10;
  (*((unsigned long*)(&r_j))) = 0;
  if ((*((unsigned long*)(&r_j))) < 10) {
    r_val6 = (*((unsigned long*)(&r_j)));
  }
  if (((*((unsigned long*)(&r_j))) < 10) && (r_val6 >= 11)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 11, &r_alloc_1b6aad345a552ecadc4ef2f80a0f897d);
  }
  if ((!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10))) || ((*((unsigned long*)(&r_j))) >= 10)) {
    (*((unsigned long*)(&r_len))) = 11;
    r_val5 = (*((unsigned long*)(&r_j)));
  }
  if (((!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10))) || ((*((unsigned long*)(&r_j))) >= 10)) && (r_val5 >= 11)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val5, 11, &r_alloc_a74a36876f5d89ac1dedf5b0e55c3dda);
  }
  if ((r_val5 < 11) && ((!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10))) || ((*((unsigned long*)(&r_j))) >= 10))) {
    ((unsigned int*)r_a)[r_val5] = r_val;
    while ((*((unsigned long*)(&r_j))) < 11) {
      (*((unsigned long*)(&r_j))) = ((*((unsigned long*)(&r_j))) + 1);
    }
  }
  if (((r_val5 < 11) && ((*((unsigned long*)(&r_j))) >= 11)) && ((!(((r_val6 >= 11) || (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) || ((*((unsigned long*)(&r_j))) >= 10))) || ((*((unsigned long*)(&r_j))) >= 10))) {
  }
  if ((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (((int)((unsigned int*)r_a)[r_val6]) < ((int)r_val))) {
    (*((unsigned long*)(&r_j))) = ((*((unsigned long*)(&r_j))) + 1);
  }
}