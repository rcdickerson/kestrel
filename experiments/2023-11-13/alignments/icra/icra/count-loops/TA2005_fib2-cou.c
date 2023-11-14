#include "assert.h"

void main() {
  int l_f11 = nondet();
  int l_f12 = nondet();
  int l_n1 = nondet();
  int l_l1 = nondet();
  int l_x1 = nondet();
  int l_i1 = nondet();
  int l_h1 = nondet();
  int r_f21 = nondet();
  int r_f22 = nondet();
  int r_n2 = nondet();
  int r_l2 = nondet();
  int r_x2 = nondet();
  int r_i2 = nondet();
  int r_h2 = nondet();
  __VERIFIER_assume((l_f11 == r_f21) && ((l_f12 == r_f22) && ((l_n1 == r_n2) && ((l_l1 == r_l2) && ((l_x1 == r_x2) && (l_i1 == r_i2))))));
  while ((l_n1 > 0) && (r_n2 > 0)) {
    l_f11 = (l_f11 + l_f12);
    l_f12 = (l_f11 - l_f12);
    l_n1 = (l_n1 - 1);
    r_f21 = (r_f21 + r_f22);
    r_f22 = (r_f21 - r_f22);
    r_n2 = (r_n2 - 1);
  }
  while (l_n1 > 0) {
    __VERIFIER_assume(!(r_n2 > 0));
    l_f11 = (l_f11 + l_f12);
    l_f12 = (l_f11 - l_f12);
    l_n1 = (l_n1 - 1);
  }
  while (r_n2 > 0) {
    __VERIFIER_assume(!(l_n1 > 0));
    r_f21 = (r_f21 + r_f22);
    r_f22 = (r_f21 - r_f22);
    r_n2 = (r_n2 - 1);
  }
  if (l_h1) {
    l_x1 = 1;
  }
  if (r_h2) {
    r_x2 = 1;
  }
  if (!l_h1) {
    l_x1 = 1;
  }
  if (!r_h2) {
    r_x2 = 1;
  }
  while ((l_i1 < l_f11) && (r_i2 < r_f21)) {
    l_l1 = (l_l1 + l_x1);
    l_i1 = (l_i1 + 1);
    r_l2 = (r_l2 + r_x2);
    r_i2 = (r_i2 + 1);
  }
  while (l_i1 < l_f11) {
    __VERIFIER_assume(!(r_i2 < r_f21));
    l_l1 = (l_l1 + l_x1);
    l_i1 = (l_i1 + 1);
  }
  while (r_i2 < r_f21) {
    __VERIFIER_assume(!(l_i1 < l_f11));
    r_l2 = (r_l2 + r_x2);
    r_i2 = (r_i2 + 1);
  }
  __VERIFIER_assert(l_l1 == r_l2);
 }
