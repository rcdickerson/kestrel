#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_a = arb_int();
  int l_b = arb_int();
  int r_a = arb_int();
  int r_b = arb_int();
  assume((l_a == r_a) && (l_b == r_b));
  int l_c = 0;
  int r_c = 0;
  while ((l_a < l_b) && (r_a < r_b)) {
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
    r_c = (r_c + (r_a * r_a));
    r_a = (r_a + 1);
    if (r_a < r_b) {
      r_c = (r_c + (r_a * r_a));
      r_a = (r_a + 1);
    }
  }
  while ((l_a < l_b) && (!(r_a < r_b))) {
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
  }
  while ((!(l_a < l_b)) && (r_a < r_b)) {
    r_c = (r_c + (r_a * r_a));
    r_a = (r_a + 1);
  }
  sassert(l_c == r_c);
 }
