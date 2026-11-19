void main(int l_a, int l_b, int l_c, int r_a, int r_b, int r_c) {
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
}