void right(unsigned int low, unsigned int h) {
    char h_var0[4];
    char low_var1[4];
    char v[4];
    char y[4];
    char i[4];
    *(unsigned int *)(&low_var1) = low;
    *(unsigned int *)(&h_var0) = h;
    *(unsigned int *)(&i) = 0;
    *(unsigned int *)(&y) = 0;
    *(unsigned int *)(&v) = 0;
    while ((int)h > (int)(*(unsigned int *)(&i)))
    {
        *(unsigned int *)(&i) = *(unsigned int *)(&i) + 1;
        *(unsigned int *)(&y) = *(unsigned int *)(&y) + *(unsigned int *)(&y);
    }
    *(unsigned int *)(&v) = 1;
    while ((int)low > (int)(*(unsigned int *)(&i)))
    {
        *(unsigned int *)(&i) = *(unsigned int *)(&i) + 1;
        *(unsigned int *)(&y) = *(unsigned int *)(&y) + *(unsigned int *)(&y);
    }
    return;
}
