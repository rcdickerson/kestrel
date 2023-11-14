#include "assert.h"

void main() {
  int l_x = nondet();
  int r_x = nondet();
  __VERIFIER_assume(l_x == r_x);
  int l_y = 0;
  int l_z = 2 * l_x;
  int l_i = 0;
  int r_y = 0;
  int r_z = r_x;
  int r_i = 0;
  while ((l_i < l_z) && (r_i < r_z)) {
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
    r_y = (r_y + r_x);
    r_i = (r_i + 1);
  }
  while (l_i < l_z) {
    __VERIFIER_assume(!(r_i < r_z));
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
  }
  while (r_i < r_z) {
    __VERIFIER_assume(!(l_i < l_z));
    r_y = (r_y + r_x);
    r_i = (r_i + 1);
  }
  r_y = (r_y * 2);
  __VERIFIER_assert(l_y == r_y);
 }
