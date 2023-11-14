#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_x = arb_int();
  int l_n = arb_int();
  int r_x = arb_int();
  int r_n = arb_int();
  assume((l_x == r_x) && (l_n == r_n));
  l_x = 0;
  int l_y = l_x;
  while (l_x <= l_n) {
    l_y = (l_y + l_f(l_y));
    l_x = (l_x + 1);
  }
  r_x = 0;
  int r_y = r_x;
  while (r_x <= r_n) {
    r_x = (r_x + 1);
    r_y = (r_y + r_f(r_y));
  }
  sassert(l_y == r_y);
 }
