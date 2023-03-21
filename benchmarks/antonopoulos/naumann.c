// The desirable loop invariant (y1 > y2 && z1 > z2 > 0)
// works only with a data-dependent alignment; when
// w1 % 2 != 0, perform a left-only iteration and when
// w2 % 3 != 0, perform a right-only iteration. If
// both are zero, iterate jointly. See the CaWh rule
// and example 6.2 in the BiKat paper.

//extern int arb_int(void);

int main(void) {
  int x = arb_int();

  rel_left();

  int y1 = x;
  int z1 = 24;
  int w1 = 0;
  while (y1 > 4) {
    if (w1 % 2 == 0) {
      z1 = z1 * y1;
      y1 = y1 - 1;
    }
    w1 = w1 + 1;
  }
  w1 = w1 + 1;

  rel_mid();

  int y2 = x;
  int z2 = 16;
  int w2 = 0;
  while (y2 > 4) {
    if (w2 % 3 == 0) {
      z2 = z2 * 2;
      y2 = y2 - 1;
    }
    w2 = w2 + 1;
  }
  w2 = w2 + 1;

  rel_right();

//  sassert(z1 > z2 && z2 > 0);
}
