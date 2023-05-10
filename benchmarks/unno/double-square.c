/* @KESTREL
 * pre:   left.x == right.x;
 * left:  left;
 * right: right;
 * post:  left.y == right.y;
 */

void left(int x, int h) {
  int z = 0;
  int y = 0;
  if(h) { z = 2*x; }
  else { z = x; }
  while (z>0) {
    z = z - 1;
    y = y+x;
  }
  if(!h) { y = 2*y; }
}

void right(int x, int h) {
  int z = 0;
  int y = 0;
  if(h) { z = 2*x; }
  else { z = x; }
  while (z>0) {
    z = z - 1;
    y = y+x;
  }
  if(!h) { y = 2*y; }
}
