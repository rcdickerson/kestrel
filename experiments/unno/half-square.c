int main(void) {

  int h = arb_int();
  int low = arb_int();

  rel_left();

  int i1 = 0;
  int y1 = 0;
  int v1 = 0;
  while (h > i1) {
    i1 = i1 + 1;
    y1 = y1 + y1;
  }
  v1 = 1;
  while (low > i1) {
    i1 = i1 + 1;
    y1 = y1 + y1;
  }

  rel_mid();

  int i2 = 0;
  int y2 = 0;
  int v2 = 0;
  while (h > i2) {
    i2 = i2 + 1;
    y2 = y2 + y2;
  }
  v2 = 1;
  while (low > i2) {
    i2 = i2 + 1;
    y2 = y2 + y2;
  }

  rel_right();
}
