#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_a[20 + 1];
  int l_b[20 + 1];
  void* r_a;
  void* r_b;
  int _i = 0;
  while (_i < 20) {
    assume((l_a[_i] == ((unsigned int*)r_a)[_i]) && (l_b[0] == ((unsigned int*)r_b)[0]));
    _i = (_i + 1);
  }
  int l_i = 1;
  int l_d[20 + 1];
  char r_n[8];
  char r_b_var1[8];
  char r_a_var2[8];
  char r_d[84];
  char r_j[8];
  long r_val5;
  long r_val6;
  long r_val7;
  long r_val8;
  (*((void**)(&r_a_var2))) = r_a;
  (*((void**)(&r_b_var1))) = r_b;
  (*((unsigned long*)(&r_n))) = 20;
  (*((unsigned long*)(&r_j))) = 1;
  r_llvm_memset_p0_i64(&r_d, 0, 84, 0);
  ((unsigned int*)(&r_d))[1] = (*((unsigned int*)r_b));
  if ((*((unsigned long*)(&r_j))) > 19) {
    ((unsigned int*)r_b)[20] = ((unsigned int*)r_a)[20];
  } else {
    r_val5 = (*((unsigned long*)(&r_j)));
  }
  if (((*((unsigned long*)(&r_j))) <= 19) && (r_val5 >= 21)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val5, 21, &r_alloc_0b8d4325adacc96c98125829e397f6bf);
  }
  if (((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) {
    r_val6 = (*((unsigned long*)(&r_j)));
  }
  if ((((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) && (r_val6 >= 21)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 21, &r_alloc_e08b8f2b0a3e293c3668d56d940f8468);
  }
  if ((((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) && (r_val6 < 21)) {
    ((unsigned int*)r_b)[r_val6] = ((unsigned int*)r_a)[r_val5];
    r_val7 = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) && (r_val6 < 21)) && (r_val7 >= 21)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val7, 21, &r_alloc_cc41d17d5a9f127d988c0a9be0945e9f);
  }
  while (l_i <= 20) {
    l_b[l_i] = l_a[l_i];
    l_d[l_i] = l_b[l_i - 1];
    l_i = (l_i + 1);
  }
  if (((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val5 < 21)) && (r_val6 < 21)) {
    r_val8 = ((*((unsigned long*)(&r_j))) + 1);
  }
  if ((((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val5 < 21)) && (r_val8 >= 21)) && (r_val6 < 21)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val8, 21, &r_alloc_2a88a997bb9f1e7a11884c35234a2edc);
  }
  if ((((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val8 < 21)) && (r_val5 < 21)) && (r_val6 < 21)) {
    ((unsigned int*)(&r_d))[r_val8] = ((unsigned int*)r_b)[r_val7];
    (*((unsigned long*)(&r_j))) = ((*((unsigned long*)(&r_j))) + 1);
  }
  int _j = 1;
  while (_j < 20) {
    sassert(l_d[_j] == ((int)((unsigned int*)(&r_d))[_j]));
    _j = (_j + 1);
  }
}