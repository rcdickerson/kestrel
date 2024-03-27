/* @KESTREL
 * pre:   left.a_in == right.a_in
       && left.b_in == right.b_in;
 * left:  f;
 * right: f;
 * post:  left.c == right.c;
 */

void _test_gen(int a, int b) {
  a = a % 100;
  b = b % 100;
  _main(a, b, a, b);
}

void f(int a_in, int b_in) {
  int a = a_in;
  int b = b_in;
  int c = 0;
  while (a < b) {
   c = c + (a * a);
   a = a + 1;
  }
}
