#include "seahorn/seahorn.h"
extern int arb_int();
void right(int a, int b, int c);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
struct literal_struct_0 llvm_smul_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void* arg0);
char alloc_28b8e771a7726746841cf729893543f2[34] = "llvm-examples/arithmetic/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_ddd654ef6743487b57c8fe6f246f34b4 = {"llvm-examples/arithmetic/right.rs", "!\000\000\000\000\000\000\000\002\000\000\000\017\000\000\000"};
struct literal_struct_1 alloc_d514bf3b79539a2c02294e96e23f2c88 = {"llvm-examples/arithmetic/right.rs", "!\000\000\000\000\000\000\000\003\000\000\000\020\000\000\000"};

void main() {
  int l_a = arb_int();
  int l_b = arb_int();
  int l_c = arb_int();
  int r_a = arb_int();
  int r_b = arb_int();
  int r_c = arb_int();
  assume((l_a == r_a) && ((l_b == r_b) && (l_c == r_c)));
  int l_sum = (l_a + l_b);
  int l_prod = (l_sum * l_c);
  char r_prod[4];
  char r_sum[4];
  char r_c_var2[4];
  char r_b_var3[4];
  char r_a_var4[4];
  struct literal_struct_0 r_call5;
  int r_val6;
  struct literal_struct_0 r_call7;
  (*((unsigned int*)(&r_a_var4))) = r_a;
  (*((unsigned int*)(&r_b_var3))) = r_b;
  (*((unsigned int*)(&r_c_var2))) = r_c;
  r_call5 = llvm_sadd_with_overflow_i32(r_a, r_b);
  r_val6 = r_call5.field0;
  if (!r_call5.field1) {
    (*((unsigned int*)(&r_sum))) = r_val6;
    r_call7 = llvm_smul_with_overflow_i32(r_val6, r_c);
  }
  if ((!r_call5.field1) && (!r_call7.field1)) {
    (*((unsigned int*)(&r_prod))) = r_call7.field0;
  }
  if ((!r_call5.field1) && r_call7.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_d514bf3b79539a2c02294e96e23f2c88);
  }
  if (r_call5.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_ddd654ef6743487b57c8fe6f246f34b4);
  }
  sassert(l_prod == (*((unsigned int*)(&r_prod))));
}