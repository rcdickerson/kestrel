#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_n = arb_int();
  int r_n = arb_int();
  assume((l_n == r_n) && ((l_n > 0) && (l_n < 100000)));
  int l_x = 0;
  int l_i = 0;
  while (l_i <= l_n) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  int r_y = 0;
  int r_j = 1;
  while (r_j <= r_n) {
    r_y = (r_y + r_j);
    r_j = (r_j + 1);
  }
  sassert(l_x == r_y);
 }
