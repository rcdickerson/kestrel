#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_high = arb_int();
  int l_low = arb_int();
  int r_high = arb_int();
  int r_low = arb_int();
  assume(l_low == r_low);
  int l_tick = 0;
  int l_i;
  int r_tick = 0;
  int r_i;
  if (l_high == 0) {
    l_i = 0;
    while (l_i < l_low) {
      l_i = (l_i + 1);
      l_tick = (l_tick + 1);
    }
  } else {l_i = l_low;
    while (l_i > 0) {
      l_i = (l_i - 1);
      l_tick = (l_tick + 1);
    }
  }
  if (r_high == 0) {
    r_i = 0;
    while (r_i < r_low) {
      r_i = (r_i + 1);
      r_tick = (r_tick + 1);
    }
  } else {r_i = r_low;
    while (r_i > 0) {
      r_i = (r_i - 1);
      r_tick = (r_tick + 1);
    }
  }
  sassert(l_tick == r_tick);
 }
