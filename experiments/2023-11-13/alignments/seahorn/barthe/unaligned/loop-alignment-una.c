#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_a[20 + 1];
  int l_b[20 + 1];
  int r_a[20 + 1];
  int r_b[20 + 1];
  int _i = 0;
  while (_i < 20) {
    assume((l_a[_i] == r_a[_i]) && (l_b[0] == r_b[0]));
    _i = (_i + 1);
  }
  int l_i = 1;
  int l_d[20 + 1];
  while (l_i <= 20) {
    l_b[l_i] = l_a[l_i];
    l_d[l_i] = l_b[l_i - 1];
    l_i = (l_i + 1);
  }
  int r_j = 1;
  int r_d[20 + 1];
  r_d[1] = r_b[0];
  while (r_j <= (20 - 1)) {
    r_b[r_j] = r_a[r_j];
    r_d[r_j + 1] = r_b[r_j];
    r_j = (r_j + 1);
  }
  r_b[20] = r_a[20];
  int _j = 1;
  while (_j < 20) {
    sassert(l_d[_j] == r_d[_j]);
    _j = (_j + 1);
  }
 }
