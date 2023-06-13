#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_n = arb_int();
  int r_n = arb_int();
  assume(l_n == r_n);
  int l_x = 0;
  int l_i = 0;
  int r_x = 0;
  int r_i = 0;
  while ((l_i <= l_n) && (r_i <= r_n)) {
    l_x = (l_x + 1);
    l_i = (l_i + 1);
    r_x = (r_x + 1);
    r_i = (r_i + 1);
    if (r_i <= r_n) {
      r_x = (r_x + 1);
      r_i = (r_i + 1);
    }
  }
  while ((l_i <= l_n) && (!(r_i <= r_n))) {
    l_x = (l_x + 1);
    l_i = (l_i + 1);
  }
  while ((!(l_i <= l_n)) && (r_i <= r_n)) {
    r_x = (r_x + 1);
    r_i = (r_i + 1);
  }
  sassert(l_x == r_x);
 }
