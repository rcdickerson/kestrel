/* @ELAENIA
 * pre: forall.N == exists.N && forall.N > 0;
 * pre_sketch: forall.N <= 4;
 * forall: left;
 * exists: right;
 * post: forall.x == exists.x;
 * aspecs:
 *   randB(max) {
 *     pre: true;
 *     post: 0 <= ret! && ret! < max;
 *   }
 * especs:
 *   randB(max) {
 *     choiceVars: n;
 *     pre: 0 <= n && n < max;
 *     post: ret! == n;
 *   }
 */

int randB(int max);

void _test_gen(int b, int c, int n, int x) {
  if (n < 0) { n = n * -1; }
  n = (n % 100) + 1;
  _main(n, n);
}

void left(int N) {
  int x = 0;
  int i = 0;
  int r = 0;
  while (i <= N ) {
    r = randB(50);
    x = x + r;
    i = i + 1;
  }
}

void right(int N) {
  int x = 0;
  int i = 1;
  x = randB(100);
  int r = 0;
  while (i <= N ) {
    _invariant("l_x == r_x");
    _invariant("l_i == r_i");
    r = randB(100);
    x = x + r;
    i = i + 1;
  }
}
