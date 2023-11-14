#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_n = arb_int();
  int l_high = arb_int();
  int r_n = arb_int();
  int r_high = arb_int();
  assume(l_n == r_n);
  int l_f1 = 1;
  int l_f2 = 0;
  int l_temp = 0;
  int r_f1 = 1;
  int r_f2 = 0;
  int r_temp = 0;
  if (l_high) {
    while (l_n > 0) {
      l_f1 = (l_f1 + l_f2);
      l_f2 = (l_f1 - l_f2);
      l_n = (l_n - 1);
    }
  } else {while (l_n > 0) {
      l_temp = l_f2;
      l_f2 = l_f1;
      l_f1 = (l_f2 + l_temp);
      l_n = (l_n - 1);
    }
  }
  if (r_high) {
    while (r_n > 0) {
      r_f1 = (r_f1 + r_f2);
      r_f2 = (r_f1 - r_f2);
      r_n = (r_n - 1);
    }
  } else {while (r_n > 0) {
      r_temp = r_f2;
      r_f2 = r_f1;
      r_f1 = (r_f2 + r_temp);
      r_n = (r_n - 1);
    }
  }
  sassert(l_f1 == r_f1);
 }
