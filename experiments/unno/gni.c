int main(void) {
  int high = arb_bool();
  int low = arb_int();

  rel_left();

  if (high) {
    int x1 = arb_int();
    if (x1 >= low) {
      return x1;
    }
    while (1);
  } else {
    int x1 = low;
    int b1 = arb_int();
    while (b1) {
      x1 = x1 + 1;
    }
    return x1;
  }

  rel_mid();

  if (high) {
    int x2 = arb_int();
    if (x2 >= low) {
      return x2;
    }
    while (1);
  } else {
    int x2 = low;
    int b2 = arb_int();
    while (b2) {
      x2 = x2 + 1;
    }
    return x2;
  }

  rel_right();
}
