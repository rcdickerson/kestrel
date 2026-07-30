void right(unsigned int arg0, unsigned int b);
void right(unsigned int arg0, unsigned int b) {
    char b_var0[4];
    char c[4];
    char a[4];
    *(unsigned int *)(&a) = arg0;
    *(unsigned int *)(&b_var0) = b;
    *(unsigned int *)(&c) = 0U;
    while ((int)(*(unsigned int *)(&a)) < (int)b)
        {
            *(unsigned int *)(&c) = *(unsigned int *)(&c) + *(unsigned int *)(&a) * *(unsigned int *)(&a);
            *(unsigned int *)(&a) = *(unsigned int *)(&a) + 1U;
        }
    return;
}
