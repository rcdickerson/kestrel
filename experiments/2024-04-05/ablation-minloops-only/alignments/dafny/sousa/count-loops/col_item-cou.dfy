
method Main(l_o1: int, l_o1_getCardSet: int, l_o1_getCardRarity: int, l_o1_getCardId: int, l_o1_cardType: int, l_o2: int, l_o2_getCardSet: int, l_o2_getCardRarity: int, l_o2_getCardId: int, l_o2_cardType: int, r_o1: int, r_o1_getCardSet: int, r_o1_getCardRarity: int, r_o1_getCardId: int, r_o1_cardType: int, r_o2: int, r_o2_getCardSet: int, r_o2_getCardRarity: int, r_o2_getCardId: int, r_o2_cardType: int)
  decreases *
 {
  assume((l_o1 == r_o2) && ((l_o1_getCardSet == r_o2_getCardSet) && ((l_o1_getCardRarity == r_o2_getCardRarity) && ((l_o1_getCardId == r_o2_getCardId) && ((l_o1_cardType == r_o2_cardType) && ((l_o2 == r_o1) && ((l_o2_getCardSet == r_o1_getCardSet) && ((l_o2_getCardRarity == r_o1_getCardRarity) && ((l_o2_getCardId == r_o1_getCardId) && (l_o2_cardType == r_o1_cardType))))))))));
  var l_ret: int;
  if (l_o1 == l_o2) {
    l_ret := 0;
  } else {
    if (l_o1_getCardSet > l_o2_getCardSet) {
      l_ret := 1;
    } else {
      if (l_o1_getCardSet < l_o2_getCardSet) {
        l_ret := (-1);
      } else {
        if (l_o1_getCardRarity < l_o2_getCardRarity) {
          l_ret := 1;
        } else {
          if (l_o1_getCardRarity > l_o2_getCardRarity) {
            l_ret := (-1);
          } else {
            if (l_o1_getCardId > l_o2_getCardId) {
              l_ret := 1;
            } else {
              if (l_o1_getCardId < l_o2_getCardId) {
                l_ret := (-1);
              } else {
                l_ret := (l_o1_cardType - l_o2_cardType);
              }
            }
          }
        }
      }
    }
  }
  var r_ret: int;
  if (r_o1 == r_o2) {
    r_ret := 0;
  } else {
    if (r_o1_getCardSet > r_o2_getCardSet) {
      r_ret := 1;
    } else {
      if (r_o1_getCardSet < r_o2_getCardSet) {
        r_ret := (-1);
      } else {
        if (r_o1_getCardRarity < r_o2_getCardRarity) {
          r_ret := 1;
        } else {
          if (r_o1_getCardRarity > r_o2_getCardRarity) {
            r_ret := (-1);
          } else {
            if (r_o1_getCardId > r_o2_getCardId) {
              r_ret := 1;
            } else {
              if (r_o1_getCardId < r_o2_getCardId) {
                r_ret := (-1);
              } else {
                r_ret := (r_o1_cardType - r_o2_cardType);
              }
            }
          }
        }
      }
    }
  }
  assert(l_ret == (-1 * r_ret));
 }
