#include "assert.h"

void main() {
  int l_x = nondet();
  int l_n = nondet();
  int r_x = nondet();
  int r_n = nondet();
  __VERIFIER_assume((l_x == r_x) && (l_n == r_n));
  l_x = 0;
  int l_y = l_x;
  r_x = 0;
  int r_y = r_x;
  while ((l_x <= l_n) && (r_x <= r_n)) {
    l_y = (l_y + l_f(l_y));
    l_x = (l_x + 1);
    r_x = (r_x + 1);
    r_y = (r_y + r_f(r_y));
  }
  while (l_x <= l_n) {
    __VERIFIER_assume(!(r_x <= r_n));
    l_y = (l_y + l_f(l_y));
    l_x = (l_x + 1);
  }
  while (r_x <= r_n) {
    __VERIFIER_assume(!(l_x <= l_n));
    r_x = (r_x + 1);
    r_y = (r_y + r_f(r_y));
  }
  __VERIFIER_assert(l_y == r_y);
 }
