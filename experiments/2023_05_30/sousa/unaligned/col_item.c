#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_o1 = arb_int();
  int l_o1_getCardSet = arb_int();
  int l_o1_getCardRarity = arb_int();
  int l_o1_getCardId = arb_int();
  int l_o1_cardType = arb_int();
  int l_o2 = arb_int();
  int l_o2_getCardSet = arb_int();
  int l_o2_getCardRarity = arb_int();
  int l_o2_getCardId = arb_int();
  int l_o2_cardType = arb_int();
  int r_o1 = arb_int();
  int r_o1_getCardSet = arb_int();
  int r_o1_getCardRarity = arb_int();
  int r_o1_getCardId = arb_int();
  int r_o1_cardType = arb_int();
  int r_o2 = arb_int();
  int r_o2_getCardSet = arb_int();
  int r_o2_getCardRarity = arb_int();
  int r_o2_getCardId = arb_int();
  int r_o2_cardType = arb_int();
  assume((l_o1 == r_o2) && ((l_o1_getCardSet == r_o2_getCardSet) && ((l_o1_getCardRarity == r_o2_getCardRarity) && ((l_o1_getCardId == r_o2_getCardId) && (l_o1_cardType == r_o2_cardType)))));
  int l_ret;
  if (l_o1 == l_o2) {
    l_ret = 0;
  } else {if (l_o1_getCardSet > l_o2_getCardSet) {
      l_ret = 1;
    } else {if (l_o1_getCardSet < l_o2_getCardSet) {
        l_ret = (-1);
      } else {if (l_o1_getCardRarity < l_o2_getCardRarity) {
          l_ret = 1;
        } else {if (l_o1_getCardRarity > l_o2_getCardRarity) {
            l_ret = (-1);
          } else {if (l_o1_getCardId > l_o2_getCardId) {
              l_ret = 1;
            } else {if (l_o1_getCardId < l_o2_getCardId) {
                l_ret = (-1);
              } else {l_ret = (l_o1_cardType - l_o2_cardType);
              }
            }
          }
        }
      }
    }
  }
  int r_ret;
  if (r_o1 == r_o2) {
    r_ret = 0;
  } else {if (r_o1_getCardSet > r_o2_getCardSet) {
      r_ret = 1;
    } else {if (r_o1_getCardSet < r_o2_getCardSet) {
        r_ret = (-1);
      } else {if (r_o1_getCardRarity < r_o2_getCardRarity) {
          r_ret = 1;
        } else {if (r_o1_getCardRarity > r_o2_getCardRarity) {
            r_ret = (-1);
          } else {if (r_o1_getCardId > r_o2_getCardId) {
              r_ret = 1;
            } else {if (r_o1_getCardId < r_o2_getCardId) {
                r_ret = (-1);
              } else {r_ret = (r_o1_cardType - r_o2_cardType);
              }
            }
          }
        }
      }
    }
  }
  sassert(l_ret == (-1 * r_ret));
 }
