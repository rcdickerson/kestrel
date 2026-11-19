void right(unsigned int low, unsigned int h);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_03a35d05e04eaf3719edd360c435efa7[35] = "llvm-examples/half-square/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_5226b2b75d0e08cb6fc5c2c41dda925a = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\f\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_f8dde4f15ee28c197639570fd35cd7b2 = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\r\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_96afc6a1128a90fa2f96d3a013ab6783 = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\a\000\000\000\r\000\000\000"};
struct literal_struct_1 alloc_154f041ad698425be7055c1e90ab35fe = {"llvm-examples/half-square/right.rs", "\"\000\000\000\000\000\000\000\b\000\000\000\r\000\000\000"};
void right(unsigned int low, unsigned int h) {
    char h_var0[4];
    char low_var1[4];
    char v[4];
    char y[4];
    char i[4];
    struct literal_struct_0 call5;
    struct literal_struct_0 call6;
    struct literal_struct_0 call7;
    struct literal_struct_0 call8;
    *(unsigned int *)(&low_var1) = low;
    *(unsigned int *)(&h_var0) = h;
    *(unsigned int *)(&i) = 0U;
    *(unsigned int *)(&y) = 0U;
    *(unsigned int *)(&v) = 0U;
    if ((int)h <= (int)(*(unsigned int *)(&i))) {
        *(unsigned int *)(&v) = 1U;
    }
    if ((int)h <= (int)(*(unsigned int *)(&i)) && (int)low <= (int)(*(unsigned int *)(&i))) {
    }
    if ((int)h <= (int)(*(unsigned int *)(&i)) && (int)low > (int)(*(unsigned int *)(&i))) {
        call6 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&i), 1U);
    }
    if ((int)h <= (int)(*(unsigned int *)(&i)) && (int)low > (int)(*(unsigned int *)(&i)) && !call6.field1) {
        *(unsigned int *)(&i) = call6.field0;
        call7 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&y), *(unsigned int *)(&y));
    }
    if ((int)h <= (int)(*(unsigned int *)(&i)) && !call7.field1 && (int)low > (int)(*(unsigned int *)(&i)) && !call6.field1) {
        *(unsigned int *)(&y) = call7.field0;
    }
    if ((int)h <= (int)(*(unsigned int *)(&i)) && call7.field1 && (int)low > (int)(*(unsigned int *)(&i)) && !call6.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_f8dde4f15ee28c197639570fd35cd7b2);
    }
    if ((int)h <= (int)(*(unsigned int *)(&i)) && (int)low > (int)(*(unsigned int *)(&i)) && call6.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_5226b2b75d0e08cb6fc5c2c41dda925a);
    }
    if ((int)h > (int)(*(unsigned int *)(&i))) {
        call5 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&i), 1U);
    }
    if ((int)h > (int)(*(unsigned int *)(&i)) && !call5.field1) {
        *(unsigned int *)(&i) = call5.field0;
        call8 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&y), *(unsigned int *)(&y));
    }
    if ((int)h > (int)(*(unsigned int *)(&i)) && !call8.field1 && !call5.field1) {
        *(unsigned int *)(&y) = call8.field0;
    }
    if ((int)h > (int)(*(unsigned int *)(&i)) && call8.field1 && !call5.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_154f041ad698425be7055c1e90ab35fe);
    }
    if ((int)h > (int)(*(unsigned int *)(&i)) && call5.field1) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_96afc6a1128a90fa2f96d3a013ab6783);
    }
}
