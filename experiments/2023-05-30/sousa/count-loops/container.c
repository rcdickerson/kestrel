#include "seahorn/seahorn.h"

extern int arb_int();

void main() {
  int l_o1_departureTimeIsBefore = arb_int();
  int l_o1_departureTime = arb_int();
  int l_o1_departureMaxDuration = arb_int();
  int l_o1_departureTransportCompany = arb_int();
  int l_o1_departureTransportType = arb_int();
  int l_o2_departureTimeIsBefore = arb_int();
  int l_o2_departureTime = arb_int();
  int l_o2_departureMaxDuration = arb_int();
  int l_o2_departureTransportCompany = arb_int();
  int l_o2_departureTransportType = arb_int();
  int r_o1_departureTimeIsBefore = arb_int();
  int r_o1_departureTime = arb_int();
  int r_o1_departureMaxDuration = arb_int();
  int r_o1_departureTransportCompany = arb_int();
  int r_o1_departureTransportType = arb_int();
  int r_o2_departureTimeIsBefore = arb_int();
  int r_o2_departureTime = arb_int();
  int r_o2_departureMaxDuration = arb_int();
  int r_o2_departureTransportCompany = arb_int();
  int r_o2_departureTransportType = arb_int();
  assume((l_o1_departureTimeIsBefore == r_o2_departureTimeIsBefore) && ((l_o1_departureTime == r_o2_departureTime) && ((l_o1_departureMaxDuration == r_o2_departureMaxDuration) && ((l_o1_departureTransportCompany == r_o2_departureTransportCompany) && ((l_o1_departureTransportType == r_o2_departureTransportType) && ((l_o2_departureTimeIsBefore == r_o1_departureTimeIsBefore) && ((l_o2_departureTime == r_o1_departureTime) && ((l_o2_departureMaxDuration == r_o1_departureMaxDuration) && ((l_o2_departureTransportCompany == r_o1_departureTransportCompany) && (l_o2_departureTransportType == r_o1_departureTransportType))))))))));
  int l_rv;
  if (l_o1_departureTime < l_o2_departureTime) {
    l_rv = (-1);
  } else {if (l_o2_departureTime < l_o1_departureTime) {
      l_rv = 1;
    } else {l_rv = 0;
    }
  }
  int r_rv;
  if (l_rv == 0) {
    if (l_o1_departureMaxDuration < l_o2_departureMaxDuration) {
      l_rv = (-1);
    } else {if (l_o1_departureMaxDuration > l_o2_departureMaxDuration) {
        l_rv = 1;
      } else {if (l_o1_departureTransportCompany < l_o2_departureTransportCompany) {
          l_rv = (-1);
        } else {if (l_o2_departureTransportCompany < l_o1_departureTransportCompany) {
            l_rv = 1;
          } else {l_rv = 0;
          }
        }
        if (l_rv == 0) {
          if (l_o1_departureTransportType < l_o2_departureTransportType) {
            l_rv = (-1);
          } else {if (l_o2_departureTransportType < l_o1_departureTransportType) {
              l_rv = 1;
            } else {l_rv = 0;
            }
          }
        }
      }
    }
  }
  if (r_o1_departureTime < r_o2_departureTime) {
    r_rv = (-1);
  } else {if (r_o2_departureTime < r_o1_departureTime) {
      r_rv = 1;
    } else {r_rv = 0;
    }
  }
  if (r_rv == 0) {
    if (r_o1_departureMaxDuration < r_o2_departureMaxDuration) {
      r_rv = (-1);
    } else {if (r_o1_departureMaxDuration > r_o2_departureMaxDuration) {
        r_rv = 1;
      } else {if (r_o1_departureTransportCompany < r_o2_departureTransportCompany) {
          r_rv = (-1);
        } else {if (r_o2_departureTransportCompany < r_o1_departureTransportCompany) {
            r_rv = 1;
          } else {r_rv = 0;
          }
        }
        if (r_rv == 0) {
          if (r_o1_departureTransportType < r_o2_departureTransportType) {
            r_rv = (-1);
          } else {if (r_o2_departureTransportType < r_o1_departureTransportType) {
              r_rv = 1;
            } else {r_rv = 0;
            }
          }
        }
      }
    }
  }
  sassert(l_rv == (-1 * r_rv));
 }
