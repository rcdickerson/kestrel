void main(int l_B, int l_C, int l_N, int l_x, int r_B, int r_C, int r_N, int r_arg3) {
  int l_i = 0;
  int l_j = 0;
  while (l_i < l_N) {
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
  }
  char r_N_var0[4];
  char r_C_var1[4];
  char r_B_var2[4];
  char r_j[4];
  char r_i[4];
  char r_x[4];
  struct literal_struct_0 r_call6;
  struct literal_struct_0 r_call7;
  struct literal_struct_0 r_call8;
  (*((unsigned int*)(&r_x))) = r_arg3;
  (*((unsigned int*)(&r_B_var2))) = r_B;
  (*((unsigned int*)(&r_C_var1))) = r_C;
  (*((unsigned int*)(&r_N_var0))) = r_N;
  (*((unsigned int*)(&r_i))) = 0;
  (*((unsigned int*)(&r_j))) = r_C;
  if (((int)(*((unsigned int*)(&r_i)))) >= ((int)r_N)) {
  } else {
    r_call6 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_x)), *((unsigned int*)(&r_j)));
  }
  if ((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_x))) = r_call6.field0;
    r_call7 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_j)), r_B);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call7.field1)) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_j))) = r_call7.field0;
    r_call8 = llvm_sadd_with_overflow_i32(*((unsigned int*)(&r_i)), 1);
  }
  if ((((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call7.field1)) && (!r_call8.field1)) && (!r_call6.field1)) {
    (*((unsigned int*)(&r_i))) = r_call8.field0;
  }
  if ((((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call7.field1)) && (!r_call6.field1)) && r_call8.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_d3a84c47372a35600e143e3b1bb6ea38);
  }
  if (((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && (!r_call6.field1)) && r_call7.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_3dba4606618aabb57e752e345bfeb066);
  }
  if ((((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) && r_call6.field1) {
    _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_9f367a284bc7ea6fe89f1d5657f4acbf);
  }
}