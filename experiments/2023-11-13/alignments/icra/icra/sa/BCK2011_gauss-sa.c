#include "assert.h"

void main() {
  int l_n = nondet();
  int r_n = nondet();
  __VERIFIER_assume((l_n == r_n) && ((l_n > 0) && (l_n < 100000)));
  int r_y = 0;
  int r_j = 1;
  int l_x = 0;
  int l_i = 0;
  if (l_i <= l_n) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  while ((l_i <= l_n) && (r_j <= r_n)) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
    r_y = (r_y + r_j);
    r_j = (r_j + 1);
  }
  while (l_i <= l_n) {
    __VERIFIER_assume(!(r_j <= r_n));
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  while (r_j <= r_n) {
    __VERIFIER_assume(!(l_i <= l_n));
    r_y = (r_y + r_j);
    r_j = (r_j + 1);
  }
  __VERIFIER_assert(l_x == r_y);
 }
