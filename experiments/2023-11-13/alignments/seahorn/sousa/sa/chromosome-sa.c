#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  float l_o1_score[10];
  float l_o2_score[10];
  float r_o1_score[10];
  float r_o2_score[10];
  int _i = 1;
  while (_i < 10) {
    assume((l_o1_score[_i] == r_o2_score[_i]) && (l_o2_score[_i] == r_o1_score[_i]));
    _i = (_i + 1);
  }
  int l_ret = -999;
  int l_comp = 0;
  int l_i = 0;
  int r_ret = -999;
  int r_comp = 0;
  int r_i = 0;
  if (l_i < 5) {
    if (l_o1_score[l_i] < l_o2_score[l_i]) {
      l_comp = (-1);
    } else {if (l_o2_score[l_i] < l_o1_score[l_i]) {
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
  if (l_i < 5) {
    if (l_o1_score[l_i] < l_o2_score[l_i]) {
      l_comp = (-1);
    } else {if (l_o2_score[l_i] < l_o1_score[l_i]) {
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
  while ((l_i < 5) && (r_i < 5)) {
    if (l_o1_score[l_i] < l_o2_score[l_i]) {
      l_comp = (-1);
    } else {if (l_o2_score[l_i] < l_o1_score[l_i]) {
        l_comp = 1;
      } else {l_comp = 0;
      }
    }
    if (l_comp != 0) {
      l_ret = l_comp;
      break;
    }
    if (r_o1_score[r_i] < r_o2_score[r_i]) {
      r_comp = (-1);
    } else {if (r_o2_score[r_i] < r_o1_score[r_i]) {
        r_comp = 1;
      } else {r_comp = 0;
      }
    }
    l_i = (l_i + 1);
    if (r_comp != 0) {
      r_ret = r_comp;
      break;
    }
    r_i = (r_i + 1);
  }
  while (l_i < 5) {
    assume(!(r_i < 5));
    if (l_o1_score[l_i] < l_o2_score[l_i]) {
      l_comp = (-1);
    } else {if (l_o2_score[l_i] < l_o1_score[l_i]) {
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
  while (r_i < 5) {
    assume(!(l_i < 5));
    if (r_o1_score[r_i] < r_o2_score[r_i]) {
      r_comp = (-1);
    } else {if (r_o2_score[r_i] < r_o1_score[r_i]) {
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
  if (l_ret == (-999)) {
    l_ret = 0;
  }
  if (r_ret == (-999)) {
    r_ret = 0;
  }
  sassert(l_ret == (-1 * r_ret));
 }
