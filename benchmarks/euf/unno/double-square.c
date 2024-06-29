/* @KESTREL
 * pre:   left.x_in == right.x_in;
 * left:  left;
 * right: right;
 * post:  left.y == right.y;
 */

void _test_gen(int x) {
  x = x % 100;
  _main(x, x);
}

void left(int x_in) {
  int x = x_in;
  int z = 0;
  int y = 0;
  z = 2*x;
  while (z>0) {
    _invariant("2 * r_y == l_y");
    _invariant("2 * r_z == l_z");
    z = z - 1;
    y = y+x;
  }
}

void right(int x_in) {
  int x = x_in;
  int z = 0;
  int y = 0;
  z = x;
  while (z>0) {
    z = z - 1;
    y = y+x;
  }
  y = 2*y;
}
