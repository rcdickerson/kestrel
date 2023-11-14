#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_a[10];
  int l_b[10];
  int l_c[10];
  int l_k = arb_int();
  int l_x = arb_int();
  int r_a[10];
  int r_b[10];
  int r_c[10];
  int r_k = arb_int();
  int r_x = arb_int();
  assume((l_k == r_k) && (l_x == r_x));
  int _i = 0;
  while (_i < 10) {
    assume((l_a[_i] == r_a[_i]) && ((l_b[_i] == r_b[_i]) && (l_c[_i] == r_c[_i])));
    _i = (_i + 1);
  }
  int l_i = 0;
  while (l_i < 10) {
    l_a[l_i] = (l_a[l_i] + l_k);
    if (l_x < 7) {
      l_b[l_i] = (l_a[l_i] * l_c[l_i]);
    } else {l_b[l_i] = (l_a[l_i - 1] * l_b[l_i - 1]);
    }
    l_i = (l_i + 1);
  }
  if (r_x < 7) {
    int r_j = 0;
    while (r_j < 10) {
      r_a[r_j] = (r_a[r_j] + r_k);
      r_b[r_j] = (r_a[r_j] * r_c[r_j]);
      r_j = (r_j + 1);
    }
  } else {int r_j = 0;
    while (r_j < 10) {
      r_a[r_j] = (r_a[r_j] + r_k);
      r_b[r_j] = (r_a[r_j - 1] * r_b[r_j - 1]);
      r_j = (r_j + 1);
    }
  }
  int _j = 0;
  while (_j < 10) {
    sassert((l_a[_j] == r_a[_j]) && ((l_b[_j] == r_b[_j]) && (l_c[_j] == r_c[_j])));
    _j = (_j + 1);
  }
 }
