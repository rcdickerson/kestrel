/* @KESTREL
 * pre:   left.n == right.n;
 * left:  left;
 * right: right;
 * post:  left.x == right.x;
 */

void left(int n) {
  int x = 0;
  int i = 0;
  while (i < n) {
    x = x + 1;
    i = i + 1;
  }
  if (x < n) {
    x = n;
  }
}

void right(int n) {
  int x = 0;
  int i = 0;
  while (i < n) {
    x = x + 1;
    i = i + 1;
  }
}
