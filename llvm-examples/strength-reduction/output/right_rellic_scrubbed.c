void right(int B, int C, int N, int arg3) {
    int C_var1;
    int B_var2;
    int j;
    int i;
    int x;
    x = arg3;
    B_var2 = B;
    C_var1 = C;
    i = 0;
    j = C;
    while ((i) < N)
    {
        x = x + j;
        j = j + B;
        i = i + 1;
    }
}
