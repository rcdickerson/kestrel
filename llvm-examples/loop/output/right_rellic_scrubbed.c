void right(unsigned int n) {
    char n_var0[4];
    char i[4];
    char sum[4];
    *(unsigned int *)(&n_var0) = n;
    *(unsigned int *)(&sum) = 0;
    *(unsigned int *)(&i) = 1;
    while ((int)(*(unsigned int *)(&i)) <= (int)n)
    {
        *(unsigned int *)(&sum) = *(unsigned int *)(&sum) + *(unsigned int *)(&i);
        *(unsigned int *)(&i) = *(unsigned int *)(&i) + 1;
    }
}
