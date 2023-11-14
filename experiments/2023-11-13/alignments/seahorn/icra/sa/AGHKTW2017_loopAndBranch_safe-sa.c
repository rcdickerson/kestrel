#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_high = arb_int();
  int l_low = arb_int();
  int r_high = arb_int();
  int r_low = arb_int();
  assume(l_low == r_low);
  int l_i = l_low;
  int l_tick = 0;
  int r_i = r_low;
  int r_tick = 0;
  if (l_low < 0) {
    while (l_i > 0) {
      l_tick = (l_tick + 1);
      l_i = (l_i - 1);
    }
  } else {l_low = (l_low + 10);
    if (l_low >= 10) {
      int l_j = l_low;
      while (l_j > 0) {
        l_j = (l_j - 1);
        l_tick = (l_tick + 1);
      }
    } else {if (l_high < 0) {
        int l_k = l_low;
        while (l_k > 0) {
          l_k = (l_k - 1);
          l_tick = (l_tick + 1);
        }
      }
    }
  }
  if (r_low < 0) {
    while (r_i > 0) {
      r_tick = (r_tick + 1);
      r_i = (r_i - 1);
    }
  } else {r_low = (r_low + 10);
    if (r_low >= 10) {
      int r_j = r_low;
      while (r_j > 0) {
        r_j = (r_j - 1);
        r_tick = (r_tick + 1);
      }
    } else {if (r_high < 0) {
        int r_k = r_low;
        while (r_k > 0) {
          r_k = (r_k - 1);
          r_tick = (r_tick + 1);
        }
      }
    }
  }
  sassert(l_tick == r_tick);
 }
