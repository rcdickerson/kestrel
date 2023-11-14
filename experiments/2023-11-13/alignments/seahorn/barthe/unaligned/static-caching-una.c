#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_a[6][4];
  int l_s[(6 - 5) + 1];
  int r_a[6][4];
  int r_s[(6 - 5) + 1];
  int _i = 0;
  while (_i < 24) {
    assume(l_a[_i] == r_a[_i]);
    _i = (_i + 1);
  }
  int _i2 = 0;
  while (_i2 < 2) {
    assume(l_s[_i2] == r_s[_i2]);
    _i2 = (_i2 + 1);
  }
  int l_i = 0;
  while (l_i < (6 - 5)) {
    l_s[l_i] = 0;
    int l_k = 0;
    while (l_k <= (5 - 1)) {
      int l_l = 0;
      while (l_l <= (4 - 1)) {
        l_s[l_i] = (l_s[l_i] + l_a[l_i + l_k][l_l]);
        l_l = (l_l + 1);
      }
    }
  }
  r_s[0] = 0;
  int r_b[6];
  int r_k = 0;
  while (r_k <= (5 - 1)) {
    r_b[r_k] = 0;
    int r_l = 0;
    while (r_l <= (4 - 1)) {
      r_b[r_k] = (r_b[r_k] + r_a[r_k][r_l]);
      r_l = (r_l + 1);
    }
    r_s[0] = (r_s[0] + r_b[r_k]);
    r_k = (r_k + 1);
  }
  int r_i = 1;
  while (r_i <= (6 - 5)) {
    r_b[(r_i + 5) - 1] = 0;
    int r_l = 0;
    while (r_l <= (4 - 1)) {
      r_b[(r_i + 5) - 1] = (r_b[(r_i + 5) - 1] + r_a[(r_i + 5) - 1][r_l]);
      r_l = (r_l + 1);
    }
    int r_z = r_b[(r_i + 5) - 1] - r_b[r_i - 1];
    r_s[r_i] = (r_s[r_i - 1] + r_z);
    r_i = (r_i + 1);
  }
  int _j = 0;
  while (_j < 6) {
    sassert(l_s[_j] == r_s[_j]);
    _j = (_j + 1);
  }
 }
