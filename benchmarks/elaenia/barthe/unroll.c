/* @ELAENIA
 * pre: forall.N == exists.N && forall.N > 0;
 * pre_sketch: forall.N <= 4;
 * forall: left;
 * exists: right;
 * post: forall.x == exists.x;
 */

void _test_gen(int b, int c, int n, int x) {
  if (n < 0) { n = n * -1; }
  n = (n % 100) + 1;
  _main(n, n);
}

void left(int N) {
  int x = 0;
  int i = 0;
  while (i <= N ) {
    _invariant("l_x == r_x");
    x = x + i;
    i = i + 1;
  }
}

void right(int N) {
  int x = 0;
  int i = 1;
  while (i <= N ) {
    x = x + i;
    i = i + 1;
  }
}
