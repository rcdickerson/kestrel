#include "seahorn/seahorn.h"
extern int arb_int();
void right(void* a);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(long arg0, long arg1, void* arg2);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_bf44ca51fc47be80b8773cb414d76a9d[36] = "llvm-examples/code-sinking/right.rs\000";
struct literal_struct_0 { void* field0; char field1[16]; } ;
struct literal_struct_0 alloc_b6a9a667e486e61363affc1a8f96404f = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\r\000\000\000\022\000\000\000"};
struct literal_struct_0 alloc_25839b1997cb2d6209d8d3c6ba0567b5 = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\016\000\000\000\023\000\000\000"};
struct literal_struct_0 alloc_f8b2f46ae7d9d9573fbd43ab55b46be9 = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\024\000\000\000\r\000\000\000"};
struct literal_struct_0 alloc_caa79b646cf59bcf219f4511c5e9fbeb = {"llvm-examples/code-sinking/right.rs", "#\000\000\000\000\000\000\000\026\000\000\000\r\000\000\000"};

void main() {
  int l_a[10 + 1];
  void* r_a;
  int _i = 0;
  while (_i < 11) {
    assume(l_a[_i] == ((unsigned int*)r_a)[_i]);
    _i = (_i + 1);
  }
  int l_max = l_a[0];
  int l_maxi = 0;
  int l_i = 0;
  while (l_i < 10) {
    if (l_max < l_a[l_i]) {
      l_max = l_a[l_i];
      l_maxi = l_i;
    }
    l_i = (l_i + 1);
  }
  char r_t[4];
  char r_n[8];
  char r_a_var2[8];
  char r_maxi[8];
  char r_max[4];
  char r_j[8];
  long r_val6;
  long r_val7;
  long r_val8;
  long r_val9;
  int r_val10;
  long r_val11;
  (*((void**)(&r_a_var2))) = r_a;
  (*((unsigned long*)(&r_n))) = 10;
  (*((unsigned long*)(&r_j))) = 0;
  (*((unsigned int*)(&r_max))) = 0;
  (*((unsigned long*)(&r_maxi))) = 0;
  if ((*((unsigned long*)(&r_j))) >= 10) {
  } else {
    if ((*((unsigned long*)(&r_j))) == 0) {
      (*((unsigned int*)(&r_max))) = (*((unsigned int*)r_a));
      (*((unsigned long*)(&r_maxi))) = 0;
    }
    r_val6 = (*((unsigned long*)(&r_j)));
  }
  if (((*((unsigned long*)(&r_j))) < 10) && (r_val6 >= 11)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 11, &alloc_b6a9a667e486e61363affc1a8f96404f);
  }
  int l_t = l_a[10];
  l_a[10] = l_max;
  l_a[l_maxi] = l_t;
  if ((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (((int)(*((unsigned int*)(&r_max)))) < ((int)((unsigned int*)r_a)[r_val6]))) {
    r_val7 = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (r_val7 >= 11)) && (((int)(*((unsigned int*)(&r_max)))) < ((int)((unsigned int*)r_a)[r_val6]))) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val7, 11, &alloc_25839b1997cb2d6209d8d3c6ba0567b5);
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val7 < 11)) && (r_val6 < 11)) && (((int)(*((unsigned int*)(&r_max)))) < ((int)((unsigned int*)r_a)[r_val6]))) {
    (*((unsigned int*)(&r_max))) = ((unsigned int*)r_a)[r_val7];
    (*((unsigned long*)(&r_maxi))) = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val6 < 11)) && ((*((unsigned long*)(&r_j))) == 10)) {
    r_val10 = ((unsigned int*)r_a)[10];
    (*((unsigned int*)(&r_t))) = r_val10;
    ((unsigned int*)r_a)[10] = (*((unsigned int*)(&r_max)));
    r_val11 = (*((unsigned long*)(&r_maxi)));
  }
  if ((((((*((unsigned long*)(&r_j))) < 10) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val6 < 11)) && (r_val11 >= 11)) && ((*((unsigned long*)(&r_j))) == 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val11, 11, &alloc_f8b2f46ae7d9d9573fbd43ab55b46be9);
  }
  if ((((((*((unsigned long*)(&r_j))) < 10) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val6 < 11)) && (r_val11 < 11)) && ((*((unsigned long*)(&r_j))) == 10)) {
    ((unsigned int*)r_a)[r_val11] = r_val10;
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val6 < 11)) && (((*((unsigned long*)(&r_j))) != 10) || (r_val11 < 11))) {
    r_val8 = (*((unsigned long*)(&r_j)));
    r_val9 = (r_val8 + 1);
  }
  if ((((((*((unsigned long*)(&r_j))) < 10) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val6 < 11)) && (r_val9 >= r_val8)) && (((*((unsigned long*)(&r_j))) != 10) || (r_val11 < 11))) {
    (*((unsigned long*)(&r_j))) = r_val9;
  }
  if ((((((*((unsigned long*)(&r_j))) < 10) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val6 < 11)) && (r_val9 < r_val8)) && (((*((unsigned long*)(&r_j))) != 10) || (r_val11 < 11))) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_caa79b646cf59bcf219f4511c5e9fbeb);
  }
  int _j = 0;
  while (_j < 11) {
    sassert(l_a[_j] == ((unsigned int*)r_a)[_j]);
    _j = (_j + 1);
  }
}