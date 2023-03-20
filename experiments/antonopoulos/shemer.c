int main(void) {
  int x = arb_int();

  rel_left();

  int y1 = 0;
  int z1 = 2 * x;
  while (z1 > 0) {
    z1 = z1 - 1;
    y1 = y1 + x;
  }

  rel_mid();

  int y2 = 0;
  int z2 = x;
  while (z2 > 0) {
    z2 = z2 - 1;
    y2 = y2 + x;
  }
  y2 = y2 * 2;

  rel_right();
}
