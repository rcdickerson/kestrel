#include "seahorn/seahorn.h"
extern int arb_int();
const float epsilon = 0.01;
void right(void* a);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(void* arg0);
void _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(long arg0, long arg1, void* arg2);
char alloc_ea4d054be0d9a3464770d70d8a04499f[34] = "llvm-examples/bubblesort/right.rs\000";
struct literal_struct_0 { void* field0; char field1[16]; } ;
struct literal_struct_0 alloc_34f116951b3139e0475b22d64721cd95 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\017\000\000\000\r\000\000\000"};
struct literal_struct_0 alloc_be3df31bfac85ed52922cd5732d661a4 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\b\000\000\000\022\000\000\000"};
struct literal_struct_0 alloc_d10824f57abd82b96f74d8a998900e37 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\b\000\000\000\020\000\000\000"};
struct literal_struct_0 alloc_c1472aaa99a0c9e01c4370a339afe9b1 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\b\000\000\000\033\000\000\000"};
struct literal_struct_0 alloc_b306f3c5835633be8c030b2750cb09fc = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\t\000\000\000\034\000\000\000"};
struct literal_struct_0 alloc_4f931d104c31d01a560c19bd84f5d18a = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\n\000\000\000\032\000\000\000"};
struct literal_struct_0 alloc_a026c78e675b1169ca6570e96453f0ba = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\n\000\000\000\030\000\000\000"};
struct literal_struct_0 alloc_991cfbf1566089e55fc7fedefbf4d17b = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\n\000\000\000\021\000\000\000"};
struct literal_struct_0 alloc_fdc502087845ea559e5dc1b3482c0afa = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\v\000\000\000\023\000\000\000"};
struct literal_struct_0 alloc_a660e85f91318953292432dd99f84179 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\v\000\000\000\021\000\000\000"};
struct literal_struct_0 alloc_67f55a38de7b934450274c42c32973d8 = {"llvm-examples/bubblesort/right.rs", "!\000\000\000\000\000\000\000\r\000\000\000\021\000\000\000"};

void main() {
  float l_a[10];
  void* r_a;
  int _i = 1;
  while (_i < 10) {
    assume(((l_a[_i] >= ((float*)r_a)[_i]) || ((((float*)r_a)[_i] - l_a[_i]) < epsilon)) && ((l_a[_i] < ((float*)r_a)[_i]) || ((l_a[_i] - ((float*)r_a)[_i]) < epsilon)));
    _i = (_i + 1);
  }
  int l_i = 0;
  while (l_i < 10) {
    int l_j = (10 - 1);
    while (l_j > l_i) {
      if (l_a[l_j - 1] > l_a[l_j]) {
        float l_temp = l_a[l_j];
        l_a[l_j] = l_a[l_j - 1];
        l_a[l_j - 1] = l_temp;
      }
      l_j = (l_j - 1);
    }
    l_i = (l_i + 1);
  }
  char r_temp[4];
  char r_n[8];
  char r_a_var2[8];
  char r_j[8];
  char r_i[8];
  long r_val5;
  long r_val6;
  long r_val7;
  long r_val8;
  long r_val9;
  long r_val10;
  long r_val11;
  float r_val12;
  long r_val13;
  long r_val14;
  long r_val15;
  long r_val16;
  long r_val17;
  (*((void**)(&r_a_var2))) = r_a;
  (*((unsigned long*)(&r_n))) = 10;
  (*((unsigned long*)(&r_i))) = 0;
  if ((*((unsigned long*)(&r_i))) >= 10) {
  } else {
    (*((unsigned long*)(&r_j))) = 9;
  }
  if (((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) <= (*((unsigned long*)(&r_i))))) {
    r_val5 = (*((unsigned long*)(&r_i)));
    r_val6 = (r_val5 + 1);
  }
  if ((((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) <= (*((unsigned long*)(&r_i))))) && (r_val6 >= r_val5)) {
    (*((unsigned long*)(&r_i))) = r_val6;
  }
  if ((((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) <= (*((unsigned long*)(&r_i))))) && (r_val6 < r_val5)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_34f116951b3139e0475b22d64721cd95);
  }
  if (((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) {
    r_val7 = (*((unsigned long*)(&r_j)));
    r_val8 = (r_val7 - 1);
  }
  if (((((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val8, 10, &alloc_d10824f57abd82b96f74d8a998900e37);
  }
  if (((((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) {
    r_val9 = (*((unsigned long*)(&r_j)));
  }
  if ((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 >= 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val9, 10, &alloc_c1472aaa99a0c9e01c4370a339afe9b1);
  }
  if (((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) {
    r_val11 = (*((unsigned long*)(&r_j)));
  }
  if ((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 >= 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val11, 10, &alloc_b306f3c5835633be8c030b2750cb09fc);
  }
  if ((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) {
    r_val12 = ((float*)r_a)[r_val11];
    (*((float*)(&r_temp))) = r_val12;
    r_val13 = (*((unsigned long*)(&r_j)));
    r_val14 = (r_val13 - 1);
  }
  if ((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val13 >= 1)) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) && (r_val14 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val14, 10, &alloc_a026c78e675b1169ca6570e96453f0ba);
  }
  if ((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) {
    r_val15 = (*((unsigned long*)(&r_j)));
  }
  if (((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) && (r_val15 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val15, 10, &alloc_991cfbf1566089e55fc7fedefbf4d17b);
  }
  if (((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val15 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) {
    ((float*)r_a)[r_val15] = ((float*)r_a)[r_val14];
    r_val16 = (*((unsigned long*)(&r_j)));
    r_val17 = (r_val16 - 1);
  }
  if (((((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val15 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) && (r_val16 >= 1)) && (r_val17 >= 10)) {
    _RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val17, 10, &alloc_a660e85f91318953292432dd99f84179);
  }
  if (((((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val15 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) && (r_val16 >= 1)) && (r_val17 < 10)) {
    ((float*)r_a)[r_val17] = r_val12;
  }
  if (((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) && ((((float*)r_a)[r_val8] <= ((float*)r_a)[r_val9]) || (!(((((((r_val13 < 1) || (((float*)r_a)[r_val8] <= ((float*)r_a)[r_val9])) || (r_val11 >= 10)) || (r_val15 >= 10)) || (r_val14 >= 10)) || (r_val17 >= 10)) || (r_val16 < 1))))) {
    r_val10 = (*((unsigned long*)(&r_j)));
  }
  if ((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val10 >= 1)) && ((((float*)r_a)[r_val8] <= ((float*)r_a)[r_val9]) || (!(((((((r_val13 < 1) || (((float*)r_a)[r_val8] <= ((float*)r_a)[r_val9])) || (r_val11 >= 10)) || (r_val15 >= 10)) || (r_val14 >= 10)) || (r_val17 >= 10)) || (r_val16 < 1))))) {
    (*((unsigned long*)(&r_j))) = (r_val10 - 1);
  }
  if ((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val10 < 1)) && ((((float*)r_a)[r_val8] <= ((float*)r_a)[r_val9]) || (!(((((((r_val13 < 1) || (((float*)r_a)[r_val8] <= ((float*)r_a)[r_val9])) || (r_val11 >= 10)) || (r_val15 >= 10)) || (r_val14 >= 10)) || (r_val17 >= 10)) || (r_val16 < 1))))) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_67f55a38de7b934450274c42c32973d8);
  }
  if ((((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val15 < 10)) && (r_val13 >= 1)) && (r_val14 < 10)) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) && (r_val16 < 1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_fdc502087845ea559e5dc1b3482c0afa);
  }
  if (((((((((*((unsigned long*)(&r_i))) < 10) && (r_val9 < 10)) && (r_val13 < 1)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 >= 1)) && (r_val8 < 10)) && (r_val11 < 10)) && (((float*)r_a)[r_val8] > ((float*)r_a)[r_val9])) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_4f931d104c31d01a560c19bd84f5d18a);
  }
  if ((((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val7 < 1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_be3df31bfac85ed52922cd5732d661a4);
  }
  int _j = 1;
  while (_j < 10) {
    sassert(((l_a[_j] >= ((float*)r_a)[_j]) || ((((float*)r_a)[_j] - l_a[_j]) < epsilon)) && ((l_a[_j] < ((float*)r_a)[_j]) || ((l_a[_j] - ((float*)r_a)[_j]) < epsilon)));
    _j = (_j + 1);
  }
}