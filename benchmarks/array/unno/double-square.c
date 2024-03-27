/* @KESTREL
 * pre:   left.x == right.x;
 * left:  left;
 * right: right;
 * post:  left.y == right.y;
 */

void left(int x) {
  int z = 0;
  int y = 0;
  z = 2*x;
  while (z>0) {
    z = z - 1;
    y = y+x;
  }
}

void right(int x) {
  int z = 0;
  int y = 0;
  z = x;
  while (z>0) {
    z = z - 1;
    y = y+x;
  }
  y = 2*y;
}
