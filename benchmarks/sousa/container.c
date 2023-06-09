/* @KESTREL
 * pre: left_o1_departureTimeIsBefore     == right_o2_departureTimeIsBefore &&
        left_o1_departureTime             == right_o2_departureTime &&
        left_o1_departureMaxDuration      == right_o2_departureMaxDuration &&
        left_o1_departureTransportCompany == right_o2_departureTransportCompany &&
        left_o1_departureTransportType    == right_o2_departureTransportType &&
        left_o2_departureTimeIsBefore     == right_o1_departureTimeIsBefore &&
        left_o2_departureTime             == right_o1_departureTime &&
        left_o2_departureMaxDuration      == right_o1_departureMaxDuration &&
        left_o2_departureTransportCompany == right_o1_departureTransportCompany &&
        left_o2_departureTransportType    == right_o1_departureTransportType;
 * left: left;
 * right: right;
 * post: left.rv == -1 * right.rv;
 */

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

void _generator(int _departureTimeIsBefore1,
                int _departureTime1,
                int _departureMaxDuration1,
                int _departureTransportCompany1,
                int _departureTransportType1,
                int _departureTimeIsBefore2,
                int _departureTime2,
                int _departureMaxDuration2,
                int _departureTransportCompany2,
                int _departureTransportType2) {
  left_o1_departureTimeIsBefore = _departureTimeIsBefore1;
  left_o1_departureTime = _departureTime1;
  left_o1_departureMaxDuration = _departureMaxDuration1;
  left_o1_departureTransportCompany = _departureTransportCompany1;
  left_o1_departureTransportType = _departureTransportType1;

  left_o2_departureTimeIsBefore = _departureTimeIsBefore2;
  left_o2_departureTime = _departureTime2;
  left_o2_departureMaxDuration = _departureMaxDuration2;
  left_o2_departureTransportCompany = _departureTransportCompany2;
  left_o2_departureTransportType = _departureTransportType2;

  right_o1_departureTimeIsBefore = _departureTimeIsBefore2;
  right_o1_departureTime = _departureTime2;
  right_o1_departureMaxDuration = _departureMaxDuration2;
  right_o1_departureTransportCompany = _departureTransportCompany2;
  right_o1_departureTransportType = _departureTransportType2;

  right_o2_departureTimeIsBefore = _departureTimeIsBefore1;
  right_o2_departureTime = _departureTime1;
  right_o2_departureMaxDuration = _departureMaxDuration1;
  right_o2_departureTransportCompany = _departureTransportCompany1;
  right_o2_departureTransportType = _departureTransportType1;
}

int left(void) {

      int rv;
      // Times
      // ---- rv = Int.compare(left_o1.departureTime, left_o2.departureTime);
      if (left_o1_departureTime < left_o2_departureTime) {
        rv = -1;
      } else if (left_o2_departureTime < left_o1_departureTime) {
        rv = 1;
      } else {
        rv = 0;
      }
      // ----
      if (rv == 0) {
          // Duration
          if (left_o1_departureMaxDuration < left_o2_departureMaxDuration) {
              rv = -1;
          }
          else if (left_o1_departureMaxDuration > left_o2_departureMaxDuration) {
              rv = 1;
          }
          else {
            // Transport company
            // ---- rv = Int.compare(left_o1.departureTransportCompany, left_o2.departureTransportCompany);
            if (left_o1_departureTransportCompany < left_o2_departureTransportCompany) {
              rv = -1;
            } else if (left_o2_departureTransportCompany < left_o1_departureTransportCompany) {
              rv = 1;
            } else {
              rv = 0;
            }
            // ----

            if (rv == 0) {
              // Transport type
              // ---- rv = Int.compare(left_o1.departureTransportType, left_o2.departureTransportType);
              if (left_o1_departureTransportType < left_o2_departureTransportType) {
                rv = -1;
              } else if (left_o2_departureTransportType < left_o1_departureTransportType) {
                rv = 1;
              } else {
                rv = 0;
              }
              // ----
            }
          }
      }
}

int right(void) {

      int rv;
      // Times
      // ---- rv = Int.compare(right_o1.departureTime, right_o2.departureTime);
      if (right_o1_departureTime < right_o2_departureTime) {
        rv = -1;
      } else if (right_o2_departureTime < right_o1_departureTime) {
        rv = 1;
      } else {
        rv = 0;
      }
      // ----
      if (rv == 0) {
          // Duration
          if (right_o1_departureMaxDuration < right_o2_departureMaxDuration) {
              rv = -1;
          }
          else if (right_o1_departureMaxDuration > right_o2_departureMaxDuration) {
              rv = 1;
          }
          else {
            // Transport company
            // ---- rv = Int.compare(right_o1.departureTransportCompany, right_o2.departureTransportCompany);
            if (right_o1_departureTransportCompany < right_o2_departureTransportCompany) {
              rv = -1;
            } else if (right_o2_departureTransportCompany < right_o1_departureTransportCompany) {
              rv = 1;
            } else {
              rv = 0;
            }
            // ----

            if (rv == 0) {
              // Transport type
              // ---- rv = Int.compare(right_o1.departureTransportType, right_o2.departureTransportType);
              if (right_o1_departureTransportType < right_o2_departureTransportType) {
                rv = -1;
              } else if (right_o2_departureTransportType < right_o1_departureTransportType) {
                rv = 1;
              } else {
                rv = 0;
              }
              // ----
            }
          }
      }
}
