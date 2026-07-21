void _test_gen(int l_a, int l_b, int l_c, int r_a, int r_b, int r_c) {
    l_a = l_a % 50;
    l_b = l_b % 50;
    l_c = l_c % 50;
    r_a = r_a % 50;
    r_b = r_b % 50;
    r_c = r_c % 50;
    _main(l_a, l_b, l_c, r_a, r_b, r_c);
}

void left(int a, int b, int c) {
    int sum = a + b;
    int prod = sum * c;
}