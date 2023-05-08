/* @KESTREL
 * pre:   left.x == right.x;
 * left:  left;
 * right: right;
 * post:  left.z > right.z;
 */

// The desirable loop invariant (y1 > y2 && z1 > z2 > 0)
// works only with a data-dependent alignment; when
// w1 % 2 != 0, perform a left-only iteration and when
// w2 % 3 != 0, perform a right-only iteration. If
// both are zero, iterate jointly. See the CaWh rule
// and example 6.2 in the BiKat paper.

void left(int x) {
  int y = x;
  int z = 24;
  int w = 0;
  while (y > 4) {
    if (w % 2 == 0) {
      z = z * y;
      y = y - 1;
    }
    w = w + 1;
  }
}

void right(int x) {
  int y = x;
  int z = 16;
  int w = 0;
  while (y > 4) {
    if (w % 3 == 0) {
      z = z * 2;
      y = y - 1;
    }
    w = w + 1;
  }
}
