void main(int l_a, int l_b, int r_arg0, int r_b) {
  int l_c = 0;
  while (l_a < l_b) {
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
  }
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
  if (((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && (!r_call3.field1)) && r_call4.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_08ea59b51ec41ad24b2b5eec37f3909f);
  }
  if ((((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) && r_call3.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_179c49ada6cb72719bfa512ac4b1923a);
  }
}