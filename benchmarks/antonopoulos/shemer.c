/* @KESTREL
 * pre:   left.x == right.x;
 * left:  left;
 * right: right;
 * post:  left.x == right.x;
 */

void left(int x) {
  int y = 0;
  int z = 2 * x;
  while (z > 0) {
    z = z - 1;
    y = y + x;
  }
}

void right(int x) {
  int y = 0;
  int z = x;
  while (z > 0) {
    z = z - 1;
    y = y + x;
  }
  y = y * 2;
}
