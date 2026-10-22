#include "seahorn/seahorn.h"
extern int arb_int();
void right(void* a, void* b);
void llvm_memset_p0_i64(void* arg0, char arg1, long arg2, char arg3);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(long arg0, long arg1, void* arg2);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_5d2ee394d6cfc9bc3d9d880d91fe8220[38] = "llvm-examples/loop-alignment/right.rs\000";
struct literal_struct_0 { void* field0; char field1[16]; } ;
struct literal_struct_0 alloc_0b8d4325adacc96c98125829e397f6bf = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\t\000\000\000\020\000\000\000"};
struct literal_struct_0 alloc_e08b8f2b0a3e293c3668d56d940f8468 = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\t\000\000\000\t\000\000\000"};
struct literal_struct_0 alloc_cc41d17d5a9f127d988c0a9be0945e9f = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\n\000\000\000\024\000\000\000"};
struct literal_struct_0 alloc_542c985c08087436c995ec63d22547ce = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\n\000\000\000\v\000\000\000"};
struct literal_struct_0 alloc_2a88a997bb9f1e7a11884c35234a2edc = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\n\000\000\000\t\000\000\000"};
struct literal_struct_0 alloc_7ca5d214dc51ac013b8e907289789fb4 = {"llvm-examples/loop-alignment/right.rs", "%\000\000\000\000\000\000\000\v\000\000\000\r\000\000\000"};

void main() {
  int l_a[20 + 1];
  int l_b[20 + 1];
  void* r_a;
  void* r_b;
  int _i = 0;
  while (_i < 20) {
    assume((l_a[_i] == ((unsigned int*)(*((unsigned int*)r_a)))[_i]) && (l_b[0] == ((unsigned int*)(*((unsigned int*)r_b)))[0]));
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
  long r_val9;
  long r_val10;
  long r_val11;
  (*((void**)(&r_a_var2))) = r_a;
  (*((void**)(&r_b_var1))) = r_b;
  (*((unsigned long*)(&r_n))) = 20;
  (*((unsigned long*)(&r_j))) = 1;
  llvm_memset_p0_i64(&r_d, 0, 84, 0);
  ((unsigned int*)(&r_d))[1] = (*((unsigned int*)r_b));
  while (l_i <= 20) {
    l_b[l_i] = l_a[l_i];
    l_d[l_i] = l_b[l_i - 1];
    l_i = (l_i + 1);
  }
  if ((*((unsigned long*)(&r_j))) > 19) {
    ((unsigned int*)r_b)[20] = ((unsigned int*)r_a)[20];
  } else {
    r_val5 = (*((unsigned long*)(&r_j)));
  }
  if (((*((unsigned long*)(&r_j))) <= 19) && (r_val5 >= 21)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val5, 21, &alloc_0b8d4325adacc96c98125829e397f6bf);
  }
  if (((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) {
    r_val6 = (*((unsigned long*)(&r_j)));
  }
  if ((((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) && (r_val6 >= 21)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 21, &alloc_e08b8f2b0a3e293c3668d56d940f8468);
  }
  if ((((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) && (r_val6 < 21)) {
    ((unsigned int*)r_b)[r_val6] = ((unsigned int*)r_a)[r_val5];
    r_val7 = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_j))) <= 19) && (r_val5 < 21)) && (r_val7 >= 21)) && (r_val6 < 21)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val7, 21, &alloc_cc41d17d5a9f127d988c0a9be0945e9f);
  }
  if (((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val5 < 21)) && (r_val6 < 21)) {
    r_val8 = (*((unsigned long*)(&r_j)));
    r_val9 = (r_val8 + 1);
  }
  if (((((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val5 < 21)) && (r_val9 >= r_val8)) && (r_val6 < 21)) && (r_val9 >= 21)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val9, 21, &alloc_2a88a997bb9f1e7a11884c35234a2edc);
  }
  if (((((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val5 < 21)) && (r_val9 >= r_val8)) && (r_val6 < 21)) && (r_val9 < 21)) {
    ((unsigned int*)(&r_d))[r_val9] = ((unsigned int*)r_b)[r_val7];
    r_val10 = (*((unsigned long*)(&r_j)));
    r_val11 = (r_val10 + 1);
  }
  if ((((((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val5 < 21)) && (r_val9 >= r_val8)) && (r_val6 < 21)) && (r_val9 < 21)) && (r_val11 >= r_val10)) {
    (*((unsigned long*)(&r_j))) = r_val11;
  }
  if ((((((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val5 < 21)) && (r_val9 >= r_val8)) && (r_val11 < r_val10)) && (r_val6 < 21)) && (r_val9 < 21)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_7ca5d214dc51ac013b8e907289789fb4);
  }
  if ((((((*((unsigned long*)(&r_j))) <= 19) && (r_val7 < 21)) && (r_val9 < r_val8)) && (r_val5 < 21)) && (r_val6 < 21)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_542c985c08087436c995ec63d22547ce);
  }
  int _j = 1;
  while (_j < 20) {
    sassert(l_d[_j] == ((int)((unsigned int*)(&r_d))[_j]));
    _j = (_j + 1);
  }
}