/* @ELAENIA
 * pre: left.B == right.B
      && left.C == right.C
      && left.N == right.N
      && left.x == right.x;
 * pre_sketch: left.N <= 4;
 * forall: left;
 * exists: right;
 * post: left.x == right.x;
 */

void _test_gen(int b, int c, int n, int x) {
  n = n % 100;
  _main(b, c, n, x, b, c, n, x);
}

void left(int B, int C, int N, int x) {
  int i = 0;
  int j = 0;
  while (i < N ) {
    j = i * B + C;
    x = x + j;
    i = i + 1;
  }
}

void right(int B, int C, int N, int x) {
  int i = 0;
  int j = C;
  while (i < N ) {
    x = x + j;
    j = j + B;
    i = i + 1;
  }
}
