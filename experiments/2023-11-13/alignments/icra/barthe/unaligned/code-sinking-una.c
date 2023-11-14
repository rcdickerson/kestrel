#include "assert.h"

void main() {
  int l_a[10 + 1];
  int r_a[10 + 1];
  int _i = 0;
  while (_i < 11) {
    __VERIFIER_assume(l_a[_i] == r_a[_i]);
    _i = (_i + 1);
  }
  int l_max = l_a[0];
  int l_maxi = 0;
  int l_i = 0;
  while (l_i < 10) {
    if (l_max < l_a[l_i]) {
      l_max = l_a[l_i];
      l_maxi = l_i;
    }
    l_i = (l_i + 1);
  }
  int l_t = l_a[10];
  l_a[10] = l_max;
  l_a[l_maxi] = l_t;
  int r_j = 0;
  int r_max;
  int r_maxi;
  while (r_j < 10) {
    if (r_j == 0) {
      r_max = r_a[0];
      r_maxi = 0;
    }
    if (r_max < r_a[r_j]) {
      r_max = r_a[r_j];
      r_maxi = r_j;
    }
    if (r_j == 10) {
      int r_t = r_a[10];
      r_a[10] = r_max;
      r_a[r_maxi] = r_t;
    }
    r_j = (r_j + 1);
  }
  int _j = 0;
  while (_j < 11) {
    __VERIFIER_assert(l_a[_j] == r_a[_j]);
    _j = (_j + 1);
  }
 }
