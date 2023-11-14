#include "seahorn/seahorn.h"
extern int arb_int();

void main() {
  int l_o1_null = arb_int();
  int l_o2_null = arb_int();
  int l_o1_fileName_null = arb_int();
  int l_o2_fileName_null = arb_int();
  int l_o1_fileName = arb_int();
  int l_o2_fileName = arb_int();
  int r_o1_null = arb_int();
  int r_o2_null = arb_int();
  int r_o1_fileName_null = arb_int();
  int r_o2_fileName_null = arb_int();
  int r_o1_fileName = arb_int();
  int r_o2_fileName = arb_int();
  assume((l_o1_null == r_o2_null) && ((l_o1_fileName_null == r_o2_fileName_null) && ((l_o1_fileName == r_o2_fileName) && ((l_o2_null == r_o1_null) && ((l_o2_fileName_null == r_o1_fileName_null) && (l_o2_fileName == r_o1_fileName))))));
  int l_result = -999;
  if (l_o1_null) {
    if (l_o2_null) {
      l_result = 0;
    } else {l_result = 1;
    }
  } else {if (l_o2_null) {
      l_result = (-1);
    }
  }
  int r_result = -999;
  if (l_result == (-999)) {
    int l_n1 = l_o1_fileName;
    int l_n2 = l_o2_fileName;
    if (l_o1_fileName_null) {
      if (l_o2_fileName_null) {
        l_result = 0;
      } else {l_result = 1;
      }
    } else {if (l_o2_fileName_null) {
        l_result = (-1);
      }
    }
    l_result = (l_n1 - l_n2);
  }
  if (r_o1_null) {
    if (r_o2_null) {
      r_result = 0;
    } else {r_result = 1;
    }
  } else {if (r_o2_null) {
      r_result = (-1);
    }
  }
  if (r_result == (-999)) {
    int r_n1 = r_o1_fileName;
    int r_n2 = r_o2_fileName;
    if (r_o1_fileName_null) {
      if (r_o2_fileName_null) {
        r_result = 0;
      } else {r_result = 1;
      }
    } else {if (r_o2_fileName_null) {
        r_result = (-1);
      }
    }
    r_result = (r_n1 - r_n2);
  }
  sassert(l_result == (-1 * r_result));
 }
