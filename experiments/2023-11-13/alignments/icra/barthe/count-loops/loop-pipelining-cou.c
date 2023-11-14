#include "assert.h"

void main() {
  int l_a[10];
  int l_b[10];
  int l_c[10];
  int r_a[10];
  int r_b[10];
  int r_c[10];
  int _i = 0;
  while (_i < 10) {
    __VERIFIER_assume((l_a[_i] == r_a[_i]) && ((l_b[_i] == r_b[_i]) && (l_c[_i] == r_c[_i])));
    _i = (_i + 1);
  }
  int l_i = 0;
  int r_j = 0;
  r_a[0] = (r_a[0] + 1);
  r_b[0] = (r_b[0] + r_a[0]);
  r_a[1] = (r_a[1] + 1);
  while ((l_i < 10) && (r_j < (10 - 2))) {
    l_a[l_i] = (l_a[l_i] + 1);
    l_b[l_i] = (l_b[l_i] + l_a[l_i]);
    l_c[l_i] = (l_c[l_i] + l_b[l_i]);
    l_i = (l_i + 1);
    r_a[r_j + 2] = (r_a[r_j + 2] + 1);
    r_b[r_j + 1] = (r_b[r_j + 1] + r_a[r_j + 1]);
    r_c[r_j] = (r_c[r_j] + r_b[r_j]);
    r_j = (r_j + 1);
  }
  while (l_i < 10) {
    __VERIFIER_assume(!(r_j < (10 - 2)));
    l_a[l_i] = (l_a[l_i] + 1);
    l_b[l_i] = (l_b[l_i] + l_a[l_i]);
    l_c[l_i] = (l_c[l_i] + l_b[l_i]);
    l_i = (l_i + 1);
  }
  while (r_j < (10 - 2)) {
    __VERIFIER_assume(!(l_i < 10));
    r_a[r_j + 2] = (r_a[r_j + 2] + 1);
    r_b[r_j + 1] = (r_b[r_j + 1] + r_a[r_j + 1]);
    r_c[r_j] = (r_c[r_j] + r_b[r_j]);
    r_j = (r_j + 1);
  }
  r_c[r_j] = (r_c[r_j] + r_b[r_j]);
  r_b[r_j + 1] = (r_b[r_j + 1] + r_a[r_j + 1]);
  r_c[r_j + 1] = (r_c[r_j + 1] + r_b[r_j + 1]);
  int _j = 0;
  while (_j < 10) {
    __VERIFIER_assert((l_a[_j] == r_a[_j]) && ((l_b[_j] == r_b[_j]) && (l_c[_j] == r_c[_j])));
    _j = (_j + 1);
  }
 }
