#include "seahorn/seahorn.h"
extern int arb_int();
void right(int x);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_443ca199dae137e72c94c49604c0250d[30] = "llvm-examples/simple/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_b39206fbe48ecb1e8d276ee35c6d01f2 = {"llvm-examples/simple/right.rs", "\035\000\000\000\000\000\000\000\002\000\000\000\025\000\000\000"};

void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  assume(l_x == r_x);
  int l_ret_val = (l_x + 1);
  char r_ret_val[4];
  char r_x_var1[4];
  struct literal_struct_0 r_call2;
  (*((unsigned int*)(&r_x_var1))) = r_x;
  r_call2 = llvm_sadd_with_overflow_i32(r_x, 1);
  if (!r_call2.field1) {
    (*((unsigned int*)(&r_ret_val))) = r_call2.field0;
  } else {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_b39206fbe48ecb1e8d276ee35c6d01f2);
  }
  sassert(l_ret_val == (*((unsigned int*)(&r_ret_val))));
}