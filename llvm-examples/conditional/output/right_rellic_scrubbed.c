void right(int age) {
    int ret_val;
    ret_val = 0;
    if (age < 65) {
        if (age <= 12) {
            ret_val = 50;
        }
    } else {
        ret_val = 20;
    }
}
