/* @KESTREL
 * pre:   left.n == right.n;
 * left:  fun;
 * right: fun;
 * post:  left.x == right.x;
 */

void _test_gen(int n) {
  n = n % 100;
  _main(n, n);
}

void fun(int n) {
  int x = 0;
  int i = 0;

  while( i <= n ) {
    _invariant("l_x == r_x");
    x = x + 1;
    i = i + 1;
  }
}
