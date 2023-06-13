#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_N = arb_int();
  int r_N = arb_int();
  assume(l_N == r_N);
  int l_x = 0;
  int l_i = 0;
  int r_x = 0;
  int r_i = 1;
  while ((l_i <= l_N) && (r_i <= r_N)) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
    if (l_i <= l_N) {
      l_x = (l_x + l_i);
      l_i = (l_i + 1);
    }
    r_x = (r_x + r_i);
    r_i = (r_i + 1);
  }
  while ((l_i <= l_N) && (!(r_i <= r_N))) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  while ((!(l_i <= l_N)) && (r_i <= r_N)) {
    r_x = (r_x + r_i);
    r_i = (r_i + 1);
  }
  sassert(l_x == r_x);
 }
