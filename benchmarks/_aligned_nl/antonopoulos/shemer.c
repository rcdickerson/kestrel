#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  int l_y = 0;
  int l_z = 2 * l_x;
  int r_y = 0;
  int r_z = r_x;
  while ((l_z > 0) && (r_z > 0)) {
    l_z = (l_z - 1);
    l_y = (l_y + l_x);
    if (l_z > 0) {
      l_z = (l_z - 1);
      l_y = (l_y + l_x);
    }
    r_z = (r_z - 1);
    r_y = (r_y + r_x);
  }
  while ((l_z > 0) && (!(r_z > 0))) {
    l_z = (l_z - 1);
    l_y = (l_y + l_x);
  }
  while ((!(l_z > 0)) && (r_z > 0)) {
    r_z = (r_z - 1);
    r_y = (r_y + r_x);
  }
  r_y = (r_y * 2);
 }
