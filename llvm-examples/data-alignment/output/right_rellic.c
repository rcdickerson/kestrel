void right(unsigned int x);
struct literal_struct_0 {
    unsigned int field0;
    unsigned char field1;
};
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_rem_overflow(void *arg0);
struct literal_struct_0 llvm_smul_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(void *arg0);
struct literal_struct_0 llvm_ssub_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(void *arg0);
struct literal_struct_0 llvm_sadd_with_overflow_i32(unsigned int arg0, unsigned int arg1);
void _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(void *arg0);
char alloc_9145327e5a54bbfe006b4c2d25b2b018[38] = "llvm-examples/data-alignment/right.rs\000";
struct literal_struct_1 {
    void *field0;
    char field1[16];
};
struct literal_struct_1 alloc_6f6e251c8165b2b3ad25bd67f27acacb = {"llvm-examples/data-alignment/right.rs", "%\000\000\000\000\000\000\000\b\000\000\000\f\000\000\000"};
struct literal_struct_1 alloc_1bf2cf61defaafc9f0504ef757ac99a0 = {"llvm-examples/data-alignment/right.rs", "%\000\000\000\000\000\000\000\t\000\000\000\021\000\000\000"};
struct literal_struct_1 alloc_da0ec900e69fa7968e3dc4ecc9ad09fe = {"llvm-examples/data-alignment/right.rs", "%\000\000\000\000\000\000\000\n\000\000\000\021\000\000\000"};
struct literal_struct_1 alloc_a3a020ade956c011435281cc89003ae5 = {"llvm-examples/data-alignment/right.rs", "%\000\000\000\000\000\000\000\f\000\000\000\r\000\000\000"};
void right(unsigned int x) {
    char x_var0[4];
    char w[4];
    char z[4];
    char y[4];
    unsigned int val4;
    struct literal_struct_0 call5;
    struct literal_struct_0 call6;
    struct literal_struct_0 call7;
    *(unsigned int *)(&x_var0) = x;
    *(unsigned int *)(&y) = x;
    *(unsigned int *)(&z) = 16U;
    *(unsigned int *)(&w) = 0U;
    if ((int)(*(unsigned int *)(&y)) <= 4) {
        return;
    } else {
        val4 = *(unsigned int *)(&w);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !(0U && val4 == 2147483648U) && (int)val4 % 3 == 0U) {
        call6 = llvm_smul_with_overflow_i32(*(unsigned int *)(&z), 2U);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !call6.field1 && !(0U && val4 == 2147483648U) && (int)val4 % 3 == 0U) {
        *(unsigned int *)(&z) = call6.field0;
        call7 = llvm_ssub_with_overflow_i32(*(unsigned int *)(&y), 1U);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !call6.field1 && !(0U && val4 == 2147483648U) && !call7.field1 && (int)val4 % 3 == 0U) {
        *(unsigned int *)(&y) = call7.field0;
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !(0U && val4 == 2147483648U) && ((int)val4 % 3 != 0U || !(call7.field1 || call6.field1 || (int)val4 % 3 != 0U))) {
        call5 = llvm_sadd_with_overflow_i32(*(unsigned int *)(&w), 1U);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !(0U && val4 == 2147483648U) && ((int)val4 % 3 != 0U || !(call7.field1 || call6.field1 || (int)val4 % 3 != 0U)) && !call5.field1) {
        *(unsigned int *)(&w) = call5.field0;
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !(0U && val4 == 2147483648U) && call5.field1 && ((int)val4 % 3 != 0U || !(call7.field1 || call6.field1 || (int)val4 % 3 != 0U))) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(&alloc_a3a020ade956c011435281cc89003ae5);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && !call6.field1 && call7.field1 && !(0U && val4 == 2147483648U) && (int)val4 % 3 == 0U) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(&alloc_da0ec900e69fa7968e3dc4ecc9ad09fe);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && call6.field1 && !(0U && val4 == 2147483648U) && (int)val4 % 3 == 0U) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(&alloc_1bf2cf61defaafc9f0504ef757ac99a0);
    }
    if ((int)(*(unsigned int *)(&y)) > 4 && 0U && val4 == 2147483648U) {
        _RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_rem_overflow(&alloc_6f6e251c8165b2b3ad25bd67f27acacb);
    }
}
