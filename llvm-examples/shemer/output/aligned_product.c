#include "seahorn/seahorn.h"
extern int arb_int();
void right(int x);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_smul_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void* arg0);
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_21c7d9cbb050990055f10e0fc57d9fc2[30] = "llvm-examples/shemer/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_1970e77da30022a9f7f157d5e3fa5a60 = {"llvm-examples/shemer/right.rs", "\035\000\000\000\000\000\000\000\v\000\000\000\t\000\000\000"};
struct literal_struct_1 alloc_1462d87ec7fbc2eb2bc1374eb756eca7 = {"llvm-examples/shemer/right.rs", "\035\000\000\000\000\000\000\000\b\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_b8e334f92a200664aac6dc1f0546a996 = {"llvm-examples/shemer/right.rs", "\035\000\000\000\000\000\000\000\t\000\000\000\r\000\000\000"};

void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  assume((l_x == r_x) && ((l_x > -2) && (l_x < 2)));
  int l_y = 0;
  int l_z = (2 * l_x);
  int l_i = 0;
  char r_z[4];
  char r_i[4];
  char r_y[4];
  struct literal_struct_0 r_call3;
  struct literal_struct_0 r_call4;
  struct literal_struct_0 r_call5;
  (*((unsigned int*)(&r_z))) = r_x;
  (*((unsigned int*)(&r_y))) = 0;
  (*((unsigned int*)(&r_i))) = 0;
  if (((int)(*((unsigned int*)(&r_i)))) >= ((int)r_x)) {
    r_call3 = llvm_smul_with_overflow_i32(*((unsigned int*)(&r_y)), 2);
  }
  if ((((int)(*((unsigned int*)(&r_i)))) >= ((int)r_x)) && (!r_call3.field1)) {
    (*((unsigned int*)(&r_y))) = r_call3.field0;
  }
  if ((((int)(*((unsigned int*)(&r_i)))) >= ((int)r_x)) && r_call3.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_1970e77da30022a9f7f157d5e3fa5a60);
  }
  if (((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) {
    r_call4 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_y)), r_x);
  }
  if ((((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) && (!r_call4.field1)) {
    (*((unsigned int*)(&r_y))) = r_call4.field0;
    r_call5 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_i)), 1);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) && (!r_call5.field1)) && (!r_call4.field1)) {
    (*((unsigned int*)(&r_i))) = r_call5.field0;
  }
  while (l_i < l_z) {
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) && r_call5.field1) && (!r_call4.field1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_b8e334f92a200664aac6dc1f0546a996);
  }
  if ((((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) && r_call4.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_1462d87ec7fbc2eb2bc1374eb756eca7);
  }
  sassert(l_y == (*((unsigned int*)(&r_y))));
}