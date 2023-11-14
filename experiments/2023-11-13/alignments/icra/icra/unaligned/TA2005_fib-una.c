#include "assert.h"

void main() {
  int l_f11 = nondet();
  int l_f12 = nondet();
  int l_n1 = nondet();
  int l_k1 = nondet();
  int l_l1 = nondet();
  int r_f21 = nondet();
  int r_f22 = nondet();
  int r_n2 = nondet();
  int r_k2 = nondet();
  int r_l2 = nondet();
  __VERIFIER_assume((l_f11 == r_f21) && ((l_f12 == r_f22) && ((l_n1 == r_n2) && ((l_k1 == r_k2) && (l_l1 == r_l2)))));
  while (l_n1 > 0) {
    l_f11 = (l_f11 + l_f12);
    l_f12 = (l_f11 - l_f12);
    l_n1 = (l_n1 - 1);
  }
  if (l_f11 > l_k1) {
    l_l1 = 1;
  } else {l_l1 = 0;
  }
  while (r_n2 > 0) {
    r_f21 = (r_f21 + r_f22);
    r_f22 = (r_f21 - r_f22);
    r_n2 = (r_n2 - 1);
  }
  if (r_f21 > r_k2) {
    r_l2 = 1;
  } else {r_l2 = 0;
  }
  __VERIFIER_assert(l_l1 == r_l2);
 }
