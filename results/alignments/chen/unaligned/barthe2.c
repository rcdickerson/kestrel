#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_n = arb_int();
  int r_n = arb_int();
  assume(l_n == r_n);
  int l_x;
  int l_i;
  l_i = 0;
  l_x = 0;
  while (l_i <= l_n) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  int r_x;
  int r_j;
  r_j = 1;
  r_x = 0;
  while (r_j <= r_n) {
    r_x = (r_x + r_j);
    r_j = (r_j + 1);
  }
  sassert(l_x == r_x);
 }
