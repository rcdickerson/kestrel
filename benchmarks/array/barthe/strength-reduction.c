/* @KESTREL
 * pre: left.B == right.B && left.C == right.C && left.N == right.N && left.x == right.x;
 * left: left;
 * right: right;
 * post: left.x == right.x;
 */

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
