#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  assume(l_x == r_x);
  int l_y = 0;
  int l_z = 2 * l_x;
  int l_i = 0;
  int r_y = 0;
  int r_z = r_x;
  int r_i = 0;
  if (l_i < l_z) {
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
  }
  if (l_i < l_z) {
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
  }
  while ((l_i < l_z) && (r_i < r_z)) {
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
    r_y = (r_y + r_x);
    r_i = (r_i + 1);
  }
  while (l_i < l_z) {
    assume(!(r_i < r_z));
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
  }
  while (r_i < r_z) {
    assume(!(l_i < l_z));
    r_y = (r_y + r_x);
    r_i = (r_i + 1);
  }
  r_y = (r_y * 2);
  sassert(l_y == r_y);
 }
