int sum_to_n(int n) {
    int var0;
    int var1;
    var1 = 0;
    var0 = 1;
    while ((var0) <= n)
        {
            var1 = var1 + var0;
            var0 = var0 + 1;
        }
    return var1;
}
