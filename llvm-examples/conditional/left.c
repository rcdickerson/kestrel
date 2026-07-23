void _test_gen(int x) {
    x = x % 50; 
    _main(x, x);
}

void left(int age) {
    int ret_val = 0;
    if (age >= 65) {
        ret_val = 20;
    } else if (age <= 12) {
        ret_val = 50;
    } 
}
