/* @ELAENIA
 * pre: forall.x_in == exists.x_in && forall.n == exists.n
     && forall.x_in >= 0 && forall.n >= 0;
 * forall: C1;
 * exists: C2;
 * post: forall.z == exists.z;
 * aspecs: any() {
 *     pre:  true;
 *     post: ret! >= 0;
 * }
 * especs:
 *   any() {
 *     choiceVars: n;
 *     pre:  n >= 0;
 *     post: ret! == n;
 * }
 */

int any();
int _any() {
  int x = rand();
  if (x < 0) { x = x * -1; }
  x = x % 20;
  return x;
}

void _test_gen(int x, int n) {
  if (x < 0) { x = x * -1; }
  if (n < 0) { n = n * -1; }
  x = x % 20;
  n = n % 20;
  _main(x, n, x, n);
}

void C1(int x_in, int n) {
  int x = x_in;
  int t = 0;
  int z = 0;
  while (x > n) {
    _invariant("l_x != l_x_in ==> l_x >= l_n");
    _invariant("l_x <= l_x_in");
    x = x - 1;
  }
  t = any();
  t = t + x;
  z = x + t;
}

void C2(int x_in, int n) {
  int x = x_in;
  int s = 0;
  int z = 0;
  s = any();
  while (x > n) {
    _invariant("r_x != r_x_in ==> l_x != l_x_in");
    _invariant("r_x >= l_x");
    x = x - 1;
  }
  z = x + s;
}
