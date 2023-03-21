int main(void) {
  int x = arb_int();
  int y = arb_int();

  rel_left();

  int x1 = x;
  while (x1 > 0) {
    x1 = x1 - y;
  }

  rel_mid();

  int x2 = x;
  while (x2 > 0) {
    x2 = x2 - 2 * y;
  }

  rel_right();
}
