/* @KESTREL
 * pre: left.N == right.N && l_N > 0;
 * left: left;
 * right: right;
 * post: left.x == right.x;
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
