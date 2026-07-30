void right(unsigned int N);
void right(unsigned int N) {
    char N_var0[4];
    char i[4];
    char x[4];
    *(unsigned int *)(&N_var0) = N;
    *(unsigned int *)(&x) = 0U;
    *(unsigned int *)(&i) = 1U;
    while ((int)(*(unsigned int *)(&i)) <= (int)N)
        {
            *(unsigned int *)(&x) = *(unsigned int *)(&x) + *(unsigned int *)(&i);
            *(unsigned int *)(&i) = *(unsigned int *)(&i) + 1U;
        }
    return;
}
