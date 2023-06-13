#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_n = arb_int();
  int l_c = arb_int();
  int r_n = arb_int();
  int r_c = arb_int();
  assume((l_n == r_n) && (l_c == r_c));
  int l_x;
  int l_i;
  int l_j;
  l_i = 0;
  l_j = 0;
  l_x = 0;
  int r_x;
  int r_i;
  int r_j;
  r_i = 0;
  r_j = r_c;
  r_x = 0;
  while ((l_i < l_n) && (r_i < r_n)) {
    l_j = ((5 * l_i) + l_c);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
    r_x = (r_x + r_j);
    r_j = (r_j + 5);
    r_i = (r_i + 1);
    if (r_i < r_n) {
      r_x = (r_x + r_j);
      r_j = (r_j + 5);
      r_i = (r_i + 1);
    }
  }
  while ((l_i < l_n) && (!(r_i < r_n))) {
    l_j = ((5 * l_i) + l_c);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
  }
  while ((!(l_i < l_n)) && (r_i < r_n)) {
    r_x = (r_x + r_j);
    r_j = (r_j + 5);
    r_i = (r_i + 1);
  }
  sassert(l_x == r_x);
 }
