/* @KESTREL
 * pre: left.age == right.age;
 * left: get_discount;
 * right: get_discount;
 * post: left.ret_val == right.ret_val;
 */
int get_discount(int age) {
    int ret_val = 0;
    if (age >= 65) {
        ret_val = 20;
    } else if (age <= 12) {
        ret_val = 50;
    } 
    return ret_val;
}
