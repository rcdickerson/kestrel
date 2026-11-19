void main(int l_x, int r_x) {
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
}