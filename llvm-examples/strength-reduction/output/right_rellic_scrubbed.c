void right(unsigned int B, unsigned int C, unsigned int N, unsigned int arg3) {
    char N_var0[4];
    char C_var1[4];
    char B_var2[4];
    char j[4];
    char i[4];
    char x[4];
    *(unsigned int *)(&x) = arg3;
    *(unsigned int *)(&B_var2) = B;
    *(unsigned int *)(&C_var1) = C;
    *(unsigned int *)(&N_var0) = N;
    *(unsigned int *)(&i) = 0;
    *(unsigned int *)(&j) = C;
    while ((int)(*(unsigned int *)(&i)) < (int)N)
    {
        *(unsigned int *)(&x) = *(unsigned int *)(&x) + *(unsigned int *)(&j);
        *(unsigned int *)(&j) = *(unsigned int *)(&j) + B;
        *(unsigned int *)(&i) = *(unsigned int *)(&i) + 1;
    }
    return;
}
