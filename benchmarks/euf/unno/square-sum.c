/* @KESTREL
 * pre:   left.a == right.a && left.b == right.b;
 * left:  f;
 * right: f;
 * post:  left.c == right.c;
 */

void _test_gen(int a, int b) {
  _main(a, b, a, b);
}

void f(int a, int b) {
  int c = 0;
  while (a < b) {
   c = c + (a * a);
   a = a + 1;
  }
}
