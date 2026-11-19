#include "seahorn/seahorn.h"
extern int arb_int();
void right(int B, int C, int N, int arg3);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_2652009fdce8cead498d02c3a4390b1c[42] = "llvm-examples/strength-reduction/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_9f367a284bc7ea6fe89f1d5657f4acbf = {"llvm-examples/strength-reduction/right.rs", ")\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_3dba4606618aabb57e752e345bfeb066 = {"llvm-examples/strength-reduction/right.rs", ")\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_d3a84c47372a35600e143e3b1bb6ea38 = {"llvm-examples/strength-reduction/right.rs", ")\000\000\000\000\000\000\000\b\000\000\000\r\000\000\000"};

void main() {
  int l_B = arb_int();
  int l_C = arb_int();
  int l_N = arb_int();
  int l_x = arb_int();
  int r_B = arb_int();
  int r_C = arb_int();
  int r_N = arb_int();
  int r_arg3 = arb_int();
  assume((l_B == r_B) && ((l_C == r_C) && ((l_N == r_N) && (l_x == r_arg3))));
  int l_i = 0;
  int l_j = 0;
  char r_N_var0[4];
  char r_C_var1[4];
  char r_B_var2[4];
  char r_j[4];
  char r_i[4];
  char r_x[4];
  struct literal_struct_0 r_call6;
  struct literal_struct_0 r_call7;
  struct literal_struct_0 r_call8;
  (*((unsigned int*)(&r_x))) = r_arg3;
  (*((unsigned int*)(&r_B_var2))) = r_B;
  (*((unsigned int*)(&r_C_var1))) = r_C;
  (*((unsigned int*)(&r_N_var0))) = r_N;
  (*((unsigned int*)(&r_i))) = 0;
  (*((unsigned int*)(&r_j))) = r_C;
  if (((int)(*((unsigned int*)(&r_i)))) >= ((int)r_N)) {
  } else {
    r_call6 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_x)), *((unsigned int*)(&r_j)));
  }
  if ((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_x))) = r_call6.field0;
    r_call7 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_j)), r_B);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call7.field1)) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_j))) = r_call7.field0;
    r_call8 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_i)), 1);
  }
  while (l_i < l_N) {
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
  }
  if ((((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call7.field1)) && (!r_call8.field1)) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_i))) = r_call8.field0;
  }
  if ((((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call7.field1)) && (!r_call6.field1)) && r_call8.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_d3a84c47372a35600e143e3b1bb6ea38);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call6.field1)) && r_call7.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_3dba4606618aabb57e752e345bfeb066);
  }
  if ((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && r_call6.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_9f367a284bc7ea6fe89f1d5657f4acbf);
  }
  sassert(l_x == (*((unsigned int*)(&r_x))));
}