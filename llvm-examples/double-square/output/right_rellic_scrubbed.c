void right(unsigned int x) {
    char x_var0[4];
    char y[4];
    char z[4];
    *(unsigned int *)(&x_var0) = x;
    *(unsigned int *)(&z) = 2 * x;
    *(unsigned int *)(&y) = 0;
    while ((int)(*(unsigned int *)(&z)) > 0)
    {
        *(unsigned int *)(&z) = *(unsigned int *)(&z) - 1;
        *(unsigned int *)(&y) = *(unsigned int *)(&y) + x;
    }
    return;
}
