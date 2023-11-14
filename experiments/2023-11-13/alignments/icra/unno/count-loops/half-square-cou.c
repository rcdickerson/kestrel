#include "assert.h"

void main() {
  int l_low = nondet();
  int l_h = nondet();
  int r_low = nondet();
  int r_h = nondet();
  __VERIFIER_assume((l_low == r_low) && ((l_low > l_h) && ((l_h > 0) && ((r_low > r_h) && (r_h > 0)))));
  int l_i = 0;
  int l_y = 0;
  int l_v = 0;
  int r_i = 0;
  int r_y = 0;
  int r_v = 0;
  while ((l_h > l_i) && (r_h > r_i)) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
    r_i = (r_i + 1);
    r_y = (r_y + r_y);
  }
  while (l_h > l_i) {
    __VERIFIER_assume(!(r_h > r_i));
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  while (r_h > r_i) {
    __VERIFIER_assume(!(l_h > l_i));
    r_i = (r_i + 1);
    r_y = (r_y + r_y);
  }
  l_v = 1;
  r_v = 1;
  while ((l_low > l_i) && (r_low > r_i)) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
    r_i = (r_i + 1);
    r_y = (r_y + r_y);
  }
  while (l_low > l_i) {
    __VERIFIER_assume(!(r_low > r_i));
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  while (r_low > r_i) {
    __VERIFIER_assume(!(l_low > l_i));
    r_i = (r_i + 1);
    r_y = (r_y + r_y);
  }
  __VERIFIER_assert(l_y == r_y);
 }
