/* @KESTREL
 * pre: left.N == right.N;
 * left: left;
 * right: right;
 * post: left.x == right.x;
 */

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
