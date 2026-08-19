void right(unsigned int a, unsigned int b, unsigned int c) {
    char prod[4];
    char sum[4];
    char c_var2[4];
    char b_var3[4];
    char a_var4[4];
    unsigned int val5;
    *(unsigned int *)(&a_var4) = a;
    *(unsigned int *)(&b_var3) = b;
    *(unsigned int *)(&c_var2) = c;
    val5 = a + b;
    *(unsigned int *)(&sum) = val5;
    *(unsigned int *)(&prod) = val5 * c;
    return;
}
