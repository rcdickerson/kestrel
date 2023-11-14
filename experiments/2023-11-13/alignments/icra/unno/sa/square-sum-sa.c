#include "assert.h"

void main() {
  int l_a = nondet();
  int l_b = nondet();
  int r_a = nondet();
  int r_b = nondet();
  __VERIFIER_assume((l_a == r_a) && (l_b == r_b));
  int l_c = 0;
  int r_c = 0;
  while ((l_a < l_b) && (r_a < r_b)) {
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
    r_c = (r_c + (r_a * r_a));
    r_a = (r_a + 1);
  }
  while (l_a < l_b) {
    __VERIFIER_assume(!(r_a < r_b));
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
  }
  while (r_a < r_b) {
    __VERIFIER_assume(!(l_a < l_b));
    r_c = (r_c + (r_a * r_a));
    r_a = (r_a + 1);
  }
  __VERIFIER_assert(l_c == r_c);
 }
