#include "seahorn/seahorn.h"
extern int arb_int();
int left_o1_departureTimeIsBefore;
int left_o1_departureTime;
int left_o1_departureMaxDuration;
int left_o1_departureTransportCompany;
int left_o1_departureTransportType;
int left_o2_departureTimeIsBefore;
int left_o2_departureTime;
int left_o2_departureMaxDuration;
int left_o2_departureTransportCompany;
int left_o2_departureTransportType;
int right_o1_departureTimeIsBefore;
int right_o1_departureTime;
int right_o1_departureMaxDuration;
int right_o1_departureTransportCompany;
int right_o1_departureTransportType;
int right_o2_departureTimeIsBefore;
int right_o2_departureTime;
int right_o2_departureMaxDuration;
int right_o2_departureTransportCompany;
int right_o2_departureTransportType;

void main() {
  assume((left_o1_departureTimeIsBefore == right_o2_departureTimeIsBefore) && ((left_o1_departureTime == right_o2_departureTime) && ((left_o1_departureMaxDuration == right_o2_departureMaxDuration) && ((left_o1_departureTransportCompany == right_o2_departureTransportCompany) && ((left_o1_departureTransportType == right_o2_departureTransportType) && ((left_o2_departureTimeIsBefore == right_o1_departureTimeIsBefore) && ((left_o2_departureTime == right_o1_departureTime) && ((left_o2_departureMaxDuration == right_o1_departureMaxDuration) && ((left_o2_departureTransportCompany == right_o1_departureTransportCompany) && (left_o2_departureTransportType == right_o1_departureTransportType))))))))));
  int l_rv;
  int r_rv;
  if (left_o1_departureTime < left_o2_departureTime) {
    l_rv = (-1);
  } else {if (left_o2_departureTime < left_o1_departureTime) {
      l_rv = 1;
    } else {l_rv = 0;
    }
  }
  if (right_o1_departureTime < right_o2_departureTime) {
    r_rv = (-1);
  } else {if (right_o2_departureTime < right_o1_departureTime) {
      r_rv = 1;
    } else {r_rv = 0;
    }
  }
  if (l_rv == 0) {
    if (left_o1_departureMaxDuration < left_o2_departureMaxDuration) {
      l_rv = (-1);
    } else {if (left_o1_departureMaxDuration > left_o2_departureMaxDuration) {
        l_rv = 1;
      } else {if (left_o1_departureTransportCompany < left_o2_departureTransportCompany) {
          l_rv = (-1);
        } else {if (left_o2_departureTransportCompany < left_o1_departureTransportCompany) {
            l_rv = 1;
          } else {l_rv = 0;
          }
        }
        if (l_rv == 0) {
          if (left_o1_departureTransportType < left_o2_departureTransportType) {
            l_rv = (-1);
          } else {if (left_o2_departureTransportType < left_o1_departureTransportType) {
              l_rv = 1;
            } else {l_rv = 0;
            }
          }
        }
      }
    }
  }
  if (r_rv == 0) {
    if (right_o1_departureMaxDuration < right_o2_departureMaxDuration) {
      r_rv = (-1);
    } else {if (right_o1_departureMaxDuration > right_o2_departureMaxDuration) {
        r_rv = 1;
      } else {if (right_o1_departureTransportCompany < right_o2_departureTransportCompany) {
          r_rv = (-1);
        } else {if (right_o2_departureTransportCompany < right_o1_departureTransportCompany) {
            r_rv = 1;
          } else {r_rv = 0;
          }
        }
        if (r_rv == 0) {
          if (right_o1_departureTransportType < right_o2_departureTransportType) {
            r_rv = (-1);
          } else {if (right_o2_departureTransportType < right_o1_departureTransportType) {
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
