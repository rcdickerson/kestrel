void main(int l_low, int l_h, int r_low, int r_h) {
  int l_i = 0;
  int l_y = 0;
  int l_v = 0;
  while (l_h > l_i) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  l_v = 1;
  while (l_low > l_i) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
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
}