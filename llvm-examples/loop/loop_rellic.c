unsigned int sum_to_n(unsigned int n);
unsigned int sum_to_n(unsigned int n) {
    char var0[4];
    char var1[4];
    *(unsigned int *)(&var1) = 0U;
    *(unsigned int *)(&var0) = 1U;
    while ((int)(*(unsigned int *)(&var0)) <= (int)n)
        {
            *(unsigned int *)(&var1) = *(unsigned int *)(&var1) + *(unsigned int *)(&var0);
            *(unsigned int *)(&var0) = *(unsigned int *)(&var0) + 1U;
        }
    return *(unsigned int *)(&var1);
}
