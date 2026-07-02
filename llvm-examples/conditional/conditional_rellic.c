unsigned int _ZN11conditional12get_discount17hf7838d63c204e4bcE(unsigned int age);
unsigned int _ZN11conditional12get_discount17hf7838d63c204e4bcE(unsigned int age) {
    char var0[4];
    if ((int)age < 65) {
        if ((int)age > 12) {
            *(unsigned int *)(&var0) = 0U;
        } else {
            *(unsigned int *)(&var0) = 50U;
        }
    } else {
        *(unsigned int *)(&var0) = 20U;
    }
    return *(unsigned int *)(&var0);
}
