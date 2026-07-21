unsigned int get_discount(unsigned int age);
unsigned int get_discount(unsigned int age) {
    char var0[4];
    *(unsigned int *)(&var0) = 0U;
    if ((int)age < 65) {
        if ((int)age <= 12) {
            *(unsigned int *)(&var0) = 50U;
        }
    } else {
        *(unsigned int *)(&var0) = 20U;
    }
    return *(unsigned int *)(&var0);
}
