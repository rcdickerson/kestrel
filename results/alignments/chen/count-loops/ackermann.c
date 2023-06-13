#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_m = arb_int();
  int l_n = arb_int();
  int r_m = arb_int();
  int r_n = arb_int();
  assume((l_m == r_m) && (l_n == r_n));
  int l_result = l_f0rec(l_m, l_n);
  int r_result = r_f1rec(r_m, r_n);
  sassert(l_ret == r_ret);
 }
