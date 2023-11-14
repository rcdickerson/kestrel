#include "assert.h"

void main() {
  int l_B = nondet();
  int l_C = nondet();
  int l_N = nondet();
  int l_x = nondet();
  int r_B = nondet();
  int r_C = nondet();
  int r_N = nondet();
  int r_x = nondet();
  __VERIFIER_assume((l_B == r_B) && ((l_C == r_C) && ((l_N == r_N) && (l_x == r_x))));
  int l_i = 0;
  int l_j = 0;
  int r_i = 0;
  int r_j = r_C;
  while ((l_i < l_N) && (r_i < r_N)) {
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
    r_x = (r_x + r_j);
    r_j = (r_j + r_B);
    r_i = (r_i + 1);
  }
  while (l_i < l_N) {
    __VERIFIER_assume(!(r_i < r_N));
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
  }
  while (r_i < r_N) {
    __VERIFIER_assume(!(l_i < l_N));
    r_x = (r_x + r_j);
    r_j = (r_j + r_B);
    r_i = (r_i + 1);
  }
  __VERIFIER_assert(l_x == r_x);
 }
