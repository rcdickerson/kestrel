#include "seahorn/seahorn.h"
extern int arb_int();
void right(int low, int h);
struct literal_struct_0 { int field0; char field1; } ;
struct literal_struct_0 llvm_sadd_with_overflow_i32(int arg0, int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void* arg0);
char alloc_03a35d05e04eaf3719edd360c435efa7[35] = "llvm-examples/half-square/right.rs\000";
struct literal_struct_1 { void* field0; char field1[16]; } ;
struct literal_struct_1 alloc_5226b2b75d0e08cb6fc5c2c41dda925a = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\f\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_f8dde4f15ee28c197639570fd35cd7b2 = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\r\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_96afc6a1128a90fa2f96d3a013ab6783 = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_154f041ad698425be7055c1e90ab35fe = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\b\000\000\000\r\000\000\000"};

void main() {
  int l_low = arb_int();
  int l_h = arb_int();
  int r_low = arb_int();
  int r_h = arb_int();
  assume((l_low == r_low) && ((l_low > l_h) && ((l_h > 0) && ((r_low > r_h) && (r_h > 0)))));
  int l_i = 0;
  int l_y = 0;
  int l_v = 0;
  char r_h_var0[4];
  char r_low_var1[4];
  char r_v[4];
  char r_y[4];
  char r_i[4];
  struct literal_struct_0 r_call5;
  struct literal_struct_0 r_call6;
  struct literal_struct_0 r_call7;
  struct literal_struct_0 r_call8;
  (*((unsigned int*)(&r_low_var1))) = r_low;
  (*((unsigned int*)(&r_h_var0))) = r_h;
  (*((unsigned int*)(&r_i))) = 0;
  (*((unsigned int*)(&r_y))) = 0;
  (*((unsigned int*)(&r_v))) = 0;
  if (((int)r_h) <= ((int)(*((unsigned int*)(&r_i))))) {
    (*((unsigned int*)(&r_v))) = 1;
  }
  if ((((int)r_h) <= ((int)(*((unsigned int*)(&r_i))))) && (((int)r_low) <= ((int)(*((unsigned int*)(&r_i)))))) {
  }
  while (l_h > l_i) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  l_v = 1;
  while (l_low > l_i) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  if ((((int)r_h) <= ((int)(*((unsigned int*)(&r_i))))) && (((int)r_low) > ((int)(*((unsigned int*)(&r_i)))))) {
    r_call6 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_i)), 1);
  }
  if (((((int)r_h) <= ((int)(*((unsigned int*)(&r_i))))) && (((int)r_low) > ((int)(*((unsigned int*)(&r_i)))))) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_i))) = r_call6.field0;
    r_call7 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_y)), *((unsigned int*)(&r_y)));
  }
  if ((((((int)r_h) <= ((int)(*((unsigned int*)(&r_i))))) && (!r_call7.field1)) && (((int)r_low) > ((int)(*((unsigned int*)(&r_i)))))) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_y))) = r_call7.field0;
  }
  if ((((((int)r_h) <= ((int)(*((unsigned int*)(&r_i))))) && r_call7.field1) && (((int)r_low) > ((int)(*((unsigned int*)(&r_i)))))) && (!r_call6.field1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_f8dde4f15ee28c197639570fd35cd7b2);
  }
  if (((((int)r_h) <= ((int)(*((unsigned int*)(&r_i))))) && (((int)r_low) > ((int)(*((unsigned int*)(&r_i)))))) && r_call6.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_5226b2b75d0e08cb6fc5c2c41dda925a);
  }
  if (((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) {
    r_call5 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_i)), 1);
  }
  if ((((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) && (!r_call5.field1)) {
    (*((unsigned int*)(&r_i))) = r_call5.field0;
    r_call8 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_y)), *((unsigned int*)(&r_y)));
  }
  if (((((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) && (!r_call8.field1)) && (!r_call5.field1)) {
    (*((unsigned int*)(&r_y))) = r_call8.field0;
  }
  if (((((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) && r_call8.field1) && (!r_call5.field1)) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_154f041ad698425be7055c1e90ab35fe);
  }
  if ((((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) && r_call5.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_96afc6a1128a90fa2f96d3a013ab6783);
  }
  sassert(l_y == (*((unsigned int*)(&r_y))));
}