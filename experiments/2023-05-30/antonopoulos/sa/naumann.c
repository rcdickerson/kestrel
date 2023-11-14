#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  assume(l_x == r_x);
  int l_y = l_x;
  int l_z = 24;
  int l_w = 0;
  int r_y = r_x;
  int r_z = 16;
  int r_w = 0;
  while ((l_y > 4) && (r_y > 4)) {
    if ((l_w % 2) == 0) {
      l_z = (l_z * l_y);
      l_y = (l_y - 1);
    }
    l_w = (l_w + 1);
    if ((r_w % 3) == 0) {
      r_z = (r_z * 2);
      r_y = (r_y - 1);
    }
    r_w = (r_w + 1);
  }
  while ((l_y > 4) && (!(r_y > 4))) {
    if ((l_w % 2) == 0) {
      l_z = (l_z * l_y);
      l_y = (l_y - 1);
    }
    l_w = (l_w + 1);
  }
  while ((!(l_y > 4)) && (r_y > 4)) {
    if ((r_w % 3) == 0) {
      r_z = (r_z * 2);
      r_y = (r_y - 1);
    }
    r_w = (r_w + 1);
  }
  sassert(l_z > r_z);
 }
