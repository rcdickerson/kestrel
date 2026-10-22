void main(int l_n, int r_n) {
  int l_sum = 0;
  int l_i = 1;
  while (l_i <= l_n) {
    l_sum = (l_sum + l_i);
    l_i = (l_i + 1);
  }
  char r_n_var0[4];
  char r_i[4];
  char r_sum[4];
  struct literal_struct_0 r_call3;
  struct literal_struct_0 r_call4;
  (*((unsigned int*)(&r_n_var0))) = r_n;
  (*((unsigned int*)(&r_sum))) = 0;
  (*((unsigned int*)(&r_i))) = 1;
  if (((int)(*((unsigned int*)(&r_i)))) > ((int)r_n)) {
  } else {
    r_call3 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_sum)), *((unsigned int*)(&r_i)));
  }
  if ((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)) && (!r_call3.field1)) {
    (*((unsigned int*)(&r_sum))) = r_call3.field0;
    r_call4 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_i)), 1);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)) && (!r_call4.field1)) && (!r_call3.field1)) {
    (*((unsigned int*)(&r_i))) = r_call4.field0;
  }
  if (((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)) && (!r_call3.field1)) && r_call4.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_83591e49dc36b934441419653b8254c2);
  }
  if ((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)) && r_call3.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_cec36e1e6db6a74003dcc27714188173);
  }
}