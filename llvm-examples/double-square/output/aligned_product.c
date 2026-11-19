#include "seahorn/seahorn.h"
extern int arb_int();
void right(int x);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_smul_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void* arg0);
struct literal_struct_0 llvm_ssub_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(void* arg0);
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_0a26641f01b909b1bcb4846ddacf2dea[37] = "llvm-examples/double-square/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_4c064889032aecdd7eb938f0d2b843a2 = {"llvm-examples/double-square/right.rs", "$\000\000\000\000\000\000\000\003\000\000\000\021\000\000\000"};
struct literal_struct_1 alloc_a67e29adf6a66efea0f5854ca0e759d3 = {"llvm-examples/double-square/right.rs", "$\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_23096a9f68e7ede8cb6db28b098d0be3 = {"llvm-examples/double-square/right.rs", "$\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};

void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  assume(l_x == r_x);
  int l_z = 0;
  int l_y = 0;
  l_z = (2 * l_x);
  char r_x_var0[4];
  char r_y[4];
  char r_z[4];
  struct literal_struct_0 r_call3;
  struct literal_struct_0 r_call4;
  struct literal_struct_0 r_call5;
  (*((unsigned int*)(&r_x_var0))) = r_x;
  r_call3 = llvm_smul_with_overflow_i32(2, r_x);
  if (!r_call3.field1) {
    (*((unsigned int*)(&r_z))) = r_call3.field0;
    (*((unsigned int*)(&r_y))) = 0;
  }
  if ((!r_call3.field1) && (((int)(*((unsigned int*)(&r_z)))) <= 0)) {
  }
  while (l_z > 0) {
    l_z = (l_z - 1);
    l_y = (l_y + l_x);
  }
  if ((!r_call3.field1) && (((int)(*((unsigned int*)(&r_z)))) > 0)) {
    r_call4 = llvm_ssub_with_overflow_i32(*((unsigned int*)(&r_z)), 1);
  }
  if (((!r_call3.field1) && (((int)(*((unsigned int*)(&r_z)))) > 0)) && (!r_call4.field1)) {
    (*((unsigned int*)(&r_z))) = r_call4.field0;
    r_call5 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_y)), r_x);
  }
  if ((((!r_call3.field1) && (((int)(*((unsigned int*)(&r_z)))) > 0)) && (!r_call4.field1)) && (!r_call5.field1)) {
    (*((unsigned int*)(&r_y))) = r_call5.field0;
  }
  if ((((!r_call3.field1) && (((int)(*((unsigned int*)(&r_z)))) > 0)) && r_call5.field1) && (!r_call4.field1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_23096a9f68e7ede8cb6db28b098d0be3);
  }
  if (((!r_call3.field1) && (((int)(*((unsigned int*)(&r_z)))) > 0)) && r_call4.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_a67e29adf6a66efea0f5854ca0e759d3);
  }
  if (r_call3.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_4c064889032aecdd7eb938f0d2b843a2);
  }
  sassert(l_y == (*((unsigned int*)(&r_y))));
}