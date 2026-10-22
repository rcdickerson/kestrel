#include "seahorn/seahorn.h"
extern int arb_int();
void right(int N);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_18989b541471998acea3ba6b5f4461ab[30] = "llvm-examples/unroll/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_008eee418d4229b5969b3d61ddac92ee = {"llvm-examples/unroll/right.rs", "\035\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_f5fb85dd27a38af5b5bac898394b9cbc = {"llvm-examples/unroll/right.rs", "\035\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};

void main() {
  int l_N = arb_int();
  int r_N = arb_int();
  assume(l_N == r_N);
  int l_x = 0;
  int l_i = 0;
  char r_N_var0[4];
  char r_i[4];
  char r_x[4];
  struct literal_struct_0 r_call3;
  struct literal_struct_0 r_call4;
  (*((unsigned int*)(&r_N_var0))) = r_N;
  (*((unsigned int*)(&r_x))) = 0;
  (*((unsigned int*)(&r_i))) = 1;
  if (((int)(*((unsigned int*)(&r_i)))) > ((int)r_N)) {
  } else {
    r_call3 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_x)), *((unsigned int*)(&r_i)));
  }
  if ((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) && (!r_call3.field1)) {
    (*((unsigned int*)(&r_x))) = r_call3.field0;
    r_call4 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_i)), 1);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) && (!r_call4.field1)) && (!r_call3.field1)) {
    (*((unsigned int*)(&r_i))) = r_call4.field0;
  }
  if (((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) && (!r_call3.field1)) && r_call4.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_f5fb85dd27a38af5b5bac898394b9cbc);
  }
  while (l_i <= l_N) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  if ((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) && r_call3.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_008eee418d4229b5969b3d61ddac92ee);
  }
  sassert(l_x == (*((unsigned int*)(&r_x))));
}