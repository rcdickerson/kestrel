void right(unsigned int x) {
    char ret_val[4];
    char x_var1[4];
    *(unsigned int *)(&x_var1) = x;
    *(unsigned int *)(&ret_val) = x + 1;
}
