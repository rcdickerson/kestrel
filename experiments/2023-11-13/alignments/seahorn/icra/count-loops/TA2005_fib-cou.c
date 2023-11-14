#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_f11 = arb_int();
  int l_f12 = arb_int();
  int l_n1 = arb_int();
  int l_k1 = arb_int();
  int l_l1 = arb_int();
  int r_f21 = arb_int();
  int r_f22 = arb_int();
  int r_n2 = arb_int();
  int r_k2 = arb_int();
  int r_l2 = arb_int();
  assume((l_f11 == r_f21) && ((l_f12 == r_f22) && ((l_n1 == r_n2) && ((l_k1 == r_k2) && (l_l1 == r_l2)))));
  while ((l_n1 > 0) && (r_n2 > 0)) {
    l_f11 = (l_f11 + l_f12);
    l_f12 = (l_f11 - l_f12);
    l_n1 = (l_n1 - 1);
    r_f21 = (r_f21 + r_f22);
    r_f22 = (r_f21 - r_f22);
    r_n2 = (r_n2 - 1);
  }
  while (l_n1 > 0) {
    assume(!(r_n2 > 0));
    l_f11 = (l_f11 + l_f12);
    l_f12 = (l_f11 - l_f12);
    l_n1 = (l_n1 - 1);
  }
  while (r_n2 > 0) {
    assume(!(l_n1 > 0));
    r_f21 = (r_f21 + r_f22);
    r_f22 = (r_f21 - r_f22);
    r_n2 = (r_n2 - 1);
  }
  if (l_f11 > l_k1) {
    l_l1 = 1;
  } else {l_l1 = 0;
  }
  if (r_f21 > r_k2) {
    r_l2 = 1;
  } else {r_l2 = 0;
  }
  sassert(l_l1 == r_l2);
 }
