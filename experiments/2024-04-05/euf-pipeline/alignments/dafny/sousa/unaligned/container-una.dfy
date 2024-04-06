
method Main(l_o1_departureTimeIsBefore: int, l_o1_departureTime: int, l_o1_departureMaxDuration: int, l_o1_departureTransportCompany: int, l_o1_departureTransportType: int, l_o2_departureTimeIsBefore: int, l_o2_departureTime: int, l_o2_departureMaxDuration: int, l_o2_departureTransportCompany: int, l_o2_departureTransportType: int, r_o1_departureTimeIsBefore: int, r_o1_departureTime: int, r_o1_departureMaxDuration: int, r_o1_departureTransportCompany: int, r_o1_departureTransportType: int, r_o2_departureTimeIsBefore: int, r_o2_departureTime: int, r_o2_departureMaxDuration: int, r_o2_departureTransportCompany: int, r_o2_departureTransportType: int)
  decreases *
 {
  assume((l_o1_departureTimeIsBefore == r_o2_departureTimeIsBefore) && ((l_o1_departureTime == r_o2_departureTime) && ((l_o1_departureMaxDuration == r_o2_departureMaxDuration) && ((l_o1_departureTransportCompany == r_o2_departureTransportCompany) && ((l_o1_departureTransportType == r_o2_departureTransportType) && ((l_o2_departureTimeIsBefore == r_o1_departureTimeIsBefore) && ((l_o2_departureTime == r_o1_departureTime) && ((l_o2_departureMaxDuration == r_o1_departureMaxDuration) && ((l_o2_departureTransportCompany == r_o1_departureTransportCompany) && (l_o2_departureTransportType == r_o1_departureTransportType))))))))));
  var l_rv: int;
  if (l_o1_departureTime < l_o2_departureTime) {
    l_rv := (-1);
  } else {
    if (l_o2_departureTime < l_o1_departureTime) {
      l_rv := 1;
    } else {
      l_rv := 0;
    }
  }
  if (l_rv == 0) {
    if (l_o1_departureMaxDuration < l_o2_departureMaxDuration) {
      l_rv := (-1);
    } else {
      if (l_o1_departureMaxDuration > l_o2_departureMaxDuration) {
        l_rv := 1;
      } else {
        if (l_o1_departureTransportCompany < l_o2_departureTransportCompany) {
          l_rv := (-1);
        } else {
          if (l_o2_departureTransportCompany < l_o1_departureTransportCompany) {
            l_rv := 1;
          } else {
            l_rv := 0;
          }
        }
        if (l_rv == 0) {
          if (l_o1_departureTransportType < l_o2_departureTransportType) {
            l_rv := (-1);
          } else {
            if (l_o2_departureTransportType < l_o1_departureTransportType) {
              l_rv := 1;
            } else {
              l_rv := 0;
            }
          }
        }
      }
    }
  }
  var r_rv: int;
  if (r_o1_departureTime < r_o2_departureTime) {
    r_rv := (-1);
  } else {
    if (r_o2_departureTime < r_o1_departureTime) {
      r_rv := 1;
    } else {
      r_rv := 0;
    }
  }
  if (r_rv == 0) {
    if (r_o1_departureMaxDuration < r_o2_departureMaxDuration) {
      r_rv := (-1);
    } else {
      if (r_o1_departureMaxDuration > r_o2_departureMaxDuration) {
        r_rv := 1;
      } else {
        if (r_o1_departureTransportCompany < r_o2_departureTransportCompany) {
          r_rv := (-1);
        } else {
          if (r_o2_departureTransportCompany < r_o1_departureTransportCompany) {
            r_rv := 1;
          } else {
            r_rv := 0;
          }
        }
        if (r_rv == 0) {
          if (r_o1_departureTransportType < r_o2_departureTransportType) {
            r_rv := (-1);
          } else {
            if (r_o2_departureTransportType < r_o1_departureTransportType) {
              r_rv := 1;
            } else {
              r_rv := 0;
            }
          }
        }
      }
    }
  }
  assert(l_rv == (-1 * r_rv));
 }
