void main(int l_N, int r_N) {
  int l_x = 0;
  int l_i = 0;
  while (l_i <= l_N) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
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
  if ((((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) && r_call3.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_008eee418d4229b5969b3d61ddac92ee);
  }
}