#include "seahorn/seahorn.h"
extern int arb_int();
void right(int arg0, int b);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_smul_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void* arg0);
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_d58fd7249401e5d7b0f8a03dedaf138b[34] = "llvm-examples/square-sum/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_179c49ada6cb72719bfa512ac4b1923a = {"llvm-examples/square-sum/right.rs", "!\000\000\000\000\000\000\000\005\000\000\000\021\000\000\000"};
struct literal_struct_1 alloc_08ea59b51ec41ad24b2b5eec37f3909f = {"llvm-examples/square-sum/right.rs", "!\000\000\000\000\000\000\000\005\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_ec107ee395ac6b4ecf0fa2ec2dc85880 = {"llvm-examples/square-sum/right.rs", "!\000\000\000\000\000\000\000\006\000\000\000\r\000\000\000"};

void main() {
  int l_a = arb_int();
  int l_b = arb_int();
  int r_arg0 = arb_int();
  int r_b = arb_int();
  assume((l_a == r_arg0) && (l_b == r_b));
  int l_c = 0;
  char r_b_var0[4];
  char r_c[4];
  char r_a[4];
  struct literal_struct_0 r_call3;
  struct literal_struct_0 r_call4;
  struct literal_struct_0 r_call5;
  (*((unsigned int*)(&r_a))) = r_arg0;
  (*((unsigned int*)(&r_b_var0))) = r_b;
  (*((unsigned int*)(&r_c))) = 0;
  if (((int)(*((unsigned int*)(&r_a)))) >= ((int)r_b)) {
  } else {
    r_call3 = llvm_smul_with_overflow_i32(*((unsigned int*)(&r_a)), *((unsigned int*)(&r_a)));
  }
  if ((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && (!r_call3.field1)) {
    r_call4 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_c)), r_call3.field0);
  }
  if (((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && (!r_call4.field1)) && (!r_call3.field1)) {
    (*((unsigned int*)(&r_c))) = r_call4.field0;
    r_call5 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_a)), 1);
  }
  if ((((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && (!r_call4.field1)) && (!r_call5.field1)) && (!r_call3.field1)) {
    (*((unsigned int*)(&r_a))) = r_call5.field0;
  }
  if ((((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && (!r_call4.field1)) && (!r_call3.field1)) && r_call5.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_ec107ee395ac6b4ecf0fa2ec2dc85880);
  }
  while (l_a < l_b) {
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
  }
  if (((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && (!r_call3.field1)) && r_call4.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_08ea59b51ec41ad24b2b5eec37f3909f);
  }
  if ((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && r_call3.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_179c49ada6cb72719bfa512ac4b1923a);
  }
  sassert(l_c == (*((unsigned int*)(&r_c))));
}