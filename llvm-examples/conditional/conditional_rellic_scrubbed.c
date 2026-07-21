int get_discount(int age) {
    int var0;
    var0 = 0;
    if (age < 65) {
        if (age <= 12) {
            var0 = 50;
        }
    } else {
        var0 = 20;
    }
    return var0;
}
