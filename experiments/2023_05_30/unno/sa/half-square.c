#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_low = arb_int();
  int l_h = arb_int();
  int r_low = arb_int();
  int r_h = arb_int();
  assume((l_low == r_low) && ((l_low > l_h) && ((l_h > 0) && ((r_low > r_h) && (r_h > 0)))));
  int l_i = 0;
  int l_y = 0;
  int l_v = 0;
  while (l_h > l_i) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  int r_i = 0;
  int r_y = 0;
  int r_v = 0;
  while (r_h > r_i) {
    r_i = (r_i + 1);
    r_y = (r_y + r_y);
  }
  r_v = 1;
  l_v = 1;
  while ((l_low > l_i) && (r_low > r_i)) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
    r_i = (r_i + 1);
    r_y = (r_y + r_y);
  }
  while ((l_low > l_i) && (!(r_low > r_i))) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  while ((!(l_low > l_i)) && (r_low > r_i)) {
    r_i = (r_i + 1);
    r_y = (r_y + r_y);
  }
  sassert(l_y == r_y);
 }
