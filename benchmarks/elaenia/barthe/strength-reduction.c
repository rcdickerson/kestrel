/* @ELAENIA
 * pre: left.B == right.B
      && left.C == right.C
      && left.N == right.N
      && left.x == right.x;
 * pre_sketch: left.N <= 4;
 * forall: left;
 * exists: right;
 * post: left.x == right.x;
 * aspecs:
 *   randEven(max) {
 *     pre: true;
 *     post: 0 <= ret! && ret! < max && ret! % 2 == 0;
 *   }
 * especs:
 *   randB(max) {
 *     choiceVars: n;
 *     pre: 0 <= n && n < max;
 *     post: ret! == n;
 *   }
 */

int randEven(int size);
int randB(int size);

void _test_gen(int b, int c, int n, int x) {
  n = n % 100;
  _main(b, c, n, x, b, c, n, x);
}

void left(int B, int C, int N, int x) {
  int i = 0;
  int j = 0;
  int r;
  while (i < N ) {
    r = randEven(100);
    j = i * B + C;
    x = x + j + r;
    i = i + 1;
  }
}

void right(int B, int C, int N, int x) {
  int i = 0;
  int j = C;
  int r;
  while (i < N ) {
    r = randB(100);
    x = x + j + r;
    j = j + B;
    i = i + 1;
  }
}
