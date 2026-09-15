void right(unsigned int age) {
    char age_var0[4];
    char ret_val[4];
    *(unsigned int *)(&age_var0) = age;
    *(unsigned int *)(&ret_val) = 0;
    if ((int)age < 65) {
        if ((int)age <= 12) {
            *(unsigned int *)(&ret_val) = 50;
        }
    } else {
        *(unsigned int *)(&ret_val) = 20;
    }
}
