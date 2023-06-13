#include "seahorn/seahorn.h"

extern int arb_int();
const int N = 10;
float left_o1_score[N];
float left_o2_score[N];
float right_o1_score[N];
float right_o2_score[N];

void main() {
  int _i = 1;
  while (_i < N) {
    assume((left_o1_score[_i] == right_o2_score[_i]) && (left_o2_score[_i] == right_o1_score[_i]));
    _i = (_i + 1);
  }
  int l_ret = -999;
  int l_comp = 0;
  int l_i = 0;
  while (l_i < 5) {
    if (left_o1_score[l_i] < left_o2_score[l_i]) {
      l_comp = (-1);
    } else {if (left_o2_score[l_i] < left_o1_score[l_i]) {
        l_comp = 1;
      } else {l_comp = 0;
      }
    }
    if (l_comp != 0) {
      l_ret = l_comp;
      break;
    }
    l_i = (l_i + 1);
  }
  int r_ret = -999;
  int r_comp = 0;
  int r_i = 0;
  while (r_i < 5) {
    if (right_o1_score[r_i] < right_o2_score[r_i]) {
      r_comp = (-1);
    } else {if (right_o2_score[r_i] < right_o1_score[r_i]) {
        r_comp = 1;
      } else {r_comp = 0;
      }
    }
    if (r_comp != 0) {
      r_ret = r_comp;
      break;
    }
    r_i = (r_i + 1);
  }
  if (r_ret == (-999)) {
    r_ret = 0;
  }
  if (l_ret == (-999)) {
    l_ret = 0;
  }
  sassert(l_ret == (-1 * r_ret));
 }
