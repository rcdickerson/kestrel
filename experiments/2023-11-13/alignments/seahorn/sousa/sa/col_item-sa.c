#include "seahorn/seahorn.h"
extern int arb_int();
int left_o1;
int left_o1_getCardSet;
int left_o1_getCardRarity;
int left_o1_getCardId;
int left_o1_cardType;
int left_o2;
int left_o2_getCardSet;
int left_o2_getCardRarity;
int left_o2_getCardId;
int left_o2_cardType;
int right_o1;
int right_o1_getCardSet;
int right_o1_getCardRarity;
int right_o1_getCardId;
int right_o1_cardType;
int right_o2;
int right_o2_getCardSet;
int right_o2_getCardRarity;
int right_o2_getCardId;
int right_o2_cardType;

void main() {
  assume((left_o1 == right_o2) && ((left_o1_getCardSet == right_o2_getCardSet) && ((left_o1_getCardRarity == right_o2_getCardRarity) && ((left_o1_getCardId == right_o2_getCardId) && ((left_o1_cardType == right_o2_cardType) && ((left_o2 == right_o1) && ((left_o2_getCardSet == right_o1_getCardSet) && ((left_o2_getCardRarity == right_o1_getCardRarity) && ((left_o2_getCardId == right_o1_getCardId) && (left_o2_cardType == right_o1_cardType))))))))));
  int l_ret;
  if (left_o1 == left_o2) {
    l_ret = 0;
  } else {if (left_o1_getCardSet > left_o2_getCardSet) {
      l_ret = 1;
    } else {if (left_o1_getCardSet < left_o2_getCardSet) {
        l_ret = (-1);
      } else {if (left_o1_getCardRarity < left_o2_getCardRarity) {
          l_ret = 1;
        } else {if (left_o1_getCardRarity > left_o2_getCardRarity) {
            l_ret = (-1);
          } else {if (left_o1_getCardId > left_o2_getCardId) {
              l_ret = 1;
            } else {if (left_o1_getCardId < left_o2_getCardId) {
                l_ret = (-1);
              } else {l_ret = (left_o1_cardType - left_o2_cardType);
              }
            }
          }
        }
      }
    }
  }
  int r_ret;
  if (right_o1 == right_o2) {
    r_ret = 0;
  } else {if (right_o1_getCardSet > right_o2_getCardSet) {
      r_ret = 1;
    } else {if (right_o1_getCardSet < right_o2_getCardSet) {
        r_ret = (-1);
      } else {if (right_o1_getCardRarity < right_o2_getCardRarity) {
          r_ret = 1;
        } else {if (right_o1_getCardRarity > right_o2_getCardRarity) {
            r_ret = (-1);
          } else {if (right_o1_getCardId > right_o2_getCardId) {
              r_ret = 1;
            } else {if (right_o1_getCardId < right_o2_getCardId) {
                r_ret = (-1);
              } else {r_ret = (right_o1_cardType - right_o2_cardType);
              }
            }
          }
        }
      }
    }
  }
  sassert(l_ret == (-1 * r_ret));
 }
