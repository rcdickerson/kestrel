void _test_gen(int x) {
    x = x % 50; 
    _main(x, x);
}

void left(int n) {
    int sum = 0;
    int i = 1;
    while (i <= n) {
        _invariant("l_sum == r_sum");
        _invariant("l_i == r_i");
        sum = sum + i;
        i = i + 1;
    }
}
