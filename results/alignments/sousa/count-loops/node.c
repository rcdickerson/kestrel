#include "seahorn/seahorn.h"

extern int arb_int();
int left_o1_contains_id;
int left_o1_get_id;
int left_o2_contains_id;
int left_o2_get_id;
int right_o1_contains_id;
int right_o1_get_id;
int right_o2_contains_id;
int right_o2_get_id;

void main() {
  assume((left_o1_contains_id == right_o2_contains_id) && ((left_o1_get_id == right_o2_get_id) && ((left_o1_contains_id == right_o2_contains_id) && (left_o1_get_id == right_o2_get_id))));
  int l_ret = -999;
  int r_ret = -999;
  if (left_o1_contains_id && left_o2_contains_id) {
    int l_order1 = left_o1_get_id;
    int l_order2 = left_o2_get_id;
    if (l_order1 < l_order2) {
      l_ret = (-1);
    } else {if (l_order1 > l_order2) {
        l_ret = 1;
      } else {l_ret = 0;
      }
    }
  }
  if (right_o1_contains_id && right_o2_contains_id) {
    int r_order1 = right_o1_get_id;
    int r_order2 = right_o2_get_id;
    if (r_order1 < r_order2) {
      r_ret = (-1);
    } else {if (r_order1 > r_order2) {
        r_ret = 1;
      } else {r_ret = 0;
      }
    }
  }
  if (l_ret == (-999)) {
    l_ret = (left_o1_get_id - left_o2_get_id);
  }
  if (r_ret == (-999)) {
    r_ret = (right_o1_get_id - right_o2_get_id);
  }
  sassert(l_ret == (-1 * r_ret));
 }
