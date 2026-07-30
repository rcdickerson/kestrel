void right(unsigned int x);
void right(unsigned int x) {
    char z[4];
    char i[4];
    char y[4];
    *(unsigned int *)(&z) = x;
    *(unsigned int *)(&y) = 0U;
    *(unsigned int *)(&i) = 0U;
    while ((int)(*(unsigned int *)(&i)) < (int)x)
        {
            *(unsigned int *)(&y) = *(unsigned int *)(&y) + x;
            *(unsigned int *)(&i) = *(unsigned int *)(&i) + 1U;
        }
    *(unsigned int *)(&y) = *(unsigned int *)(&y) * 2U;
    return;
}
