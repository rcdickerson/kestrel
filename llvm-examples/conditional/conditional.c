int get_discount(int age) {
    if (age >= 65) {
        return 20;
    } else if (age <= 12) {
        return 50;
    } else {
        return 0;
    }
}