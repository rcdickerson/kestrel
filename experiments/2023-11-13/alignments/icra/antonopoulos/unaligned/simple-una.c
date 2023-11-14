#include "assert.h"

void main() {
  int l_n = nondet();
  int r_n = nondet();
  __VERIFIER_assume(l_n == r_n);
  int l_x = 0;
  int l_i = 0;
  while (l_i <= l_n) {
    l_x = (l_x + 1);
    l_i = (l_i + 1);
  }
  int r_x = 0;
  int r_i = 0;
  while (r_i <= r_n) {
    r_x = (r_x + 1);
    r_i = (r_i + 1);
  }
  __VERIFIER_assert(l_x == r_x);
 }
