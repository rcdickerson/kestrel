#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_n = arb_int();
  int r_n = arb_int();
  assume(l_n == r_n);
  int l_i;
  int l_x = 1;
  l_i = 1;
  while (l_i <= l_n) {
    l_x = (l_x * 1);
    l_i = (l_i + 1);
  }
  l_i = 0;
  while (l_i <= l_n) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  l_i = 1;
  while (l_i <= l_n) {
    l_x = (l_x * 2);
    l_i = (l_i + 1);
  }
  int r_i;
  int r_x = 1;
  r_i = 1;
  while (r_i <= r_n) {
    r_x = (r_x * 1);
    r_i = (r_i + 1);
  }
  r_i = 1;
  while (r_i <= r_n) {
    r_x = (r_x + r_i);
    r_i = (r_i + 1);
  }
  r_i = 1;
  while (r_i <= r_n) {
    r_x = (r_x * 2);
    r_i = (r_i + 1);
  }
  sassert(l_x == r_x);
 }
