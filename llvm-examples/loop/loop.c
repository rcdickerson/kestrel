/* @KESTREL
 * pre: left.n == right.n;
 * left: sum_to_n;
 * right: sum_to_n;
 * post: left.sum == right.sum;
 */
int sum_to_n(int n) {
    int sum = 0;
    int i = 1;
    while (i <= n) {
        sum = sum + i;
        i = i + 1;
    }
    return sum;
}
