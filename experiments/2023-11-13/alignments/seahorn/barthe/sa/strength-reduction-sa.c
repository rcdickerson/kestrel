#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_B = arb_int();
  int l_C = arb_int();
  int l_N = arb_int();
  int l_x = arb_int();
  int r_B = arb_int();
  int r_C = arb_int();
  int r_N = arb_int();
  int r_x = arb_int();
  assume((l_B == r_B) && ((l_C == r_C) && ((l_N == r_N) && (l_x == r_x))));
  int l_i = 0;
  int l_j = 0;
  int r_i = 0;
  int r_j = r_C;
  while ((l_i < l_N) && (r_i < r_N)) {
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
    r_x = (r_x + r_j);
    r_j = (r_j + r_B);
    r_i = (r_i + 1);
  }
  while (l_i < l_N) {
    assume(!(r_i < r_N));
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
  }
  while (r_i < r_N) {
    assume(!(l_i < l_N));
    r_x = (r_x + r_j);
    r_j = (r_j + r_B);
    r_i = (r_i + 1);
  }
  sassert(l_x == r_x);
 }
