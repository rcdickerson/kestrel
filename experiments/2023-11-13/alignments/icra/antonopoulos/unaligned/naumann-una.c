#include "assert.h"

void main() {
  int l_x = nondet();
  int r_x = nondet();
  __VERIFIER_assume(l_x == r_x);
  int l_y = l_x;
  int l_z = 24;
  int l_w = 0;
  while (l_y > 4) {
    if ((l_w % 2) == 0) {
      l_z = (l_z * l_y);
      l_y = (l_y - 1);
    }
    l_w = (l_w + 1);
  }
  int r_y = r_x;
  int r_z = 16;
  int r_w = 0;
  while (r_y > 4) {
    if ((r_w % 3) == 0) {
      r_z = (r_z * 2);
      r_y = (r_y - 1);
    }
    r_w = (r_w + 1);
  }
  __VERIFIER_assert(l_z > r_z);
 }
