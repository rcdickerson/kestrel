/* @KESTREL
 * pre:   left.x == right.x;
 * left:  left;
 * right: right;
 * post:  left.y == right.y;
 */

void left(int x) {
  int y = 0;
  int z = 2 * x;
  int i = 0;
  while (i < z) {
    y = y + x;
    i = i + 1;
  }
}

void right(int x) {
  int y = 0;
  int z = x;
  int i = 0;
  while (i < z) {
    y = y + x;
    i = i + 1;
  }
  y = y * 2;
}
