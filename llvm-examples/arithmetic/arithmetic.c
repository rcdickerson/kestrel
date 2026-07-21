/* @KESTREL
 * pre: left.a == right.a && left.b == right.b && left.c == right.c;
 * left: compute_c;
 * right: compute_rust;
 * post: left.prod == right.prod;
 */

int compute_c(int a, int b, int c) {
    int sum = a + b;
    int prod = sum * c;
}