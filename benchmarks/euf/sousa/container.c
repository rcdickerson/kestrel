/* @KESTREL
 * pre: left.o1_departureTimeIsBefore     == right.o2_departureTimeIsBefore &&
        left.o1_departureTime             == right.o2_departureTime &&
        left.o1_departureMaxDuration      == right.o2_departureMaxDuration &&
        left.o1_departureTransportCompany == right.o2_departureTransportCompany &&
        left.o1_departureTransportType    == right.o2_departureTransportType &&
        left.o2_departureTimeIsBefore     == right.o1_departureTimeIsBefore &&
        left.o2_departureTime             == right.o1_departureTime &&
        left.o2_departureMaxDuration      == right.o1_departureMaxDuration &&
        left.o2_departureTransportCompany == right.o1_departureTransportCompany &&
        left.o2_departureTransportType    == right.o1_departureTransportType;
 * left: compare;
 * right: compare;
 * post: left.rv == -1 * right.rv;
 */

void _test_gen(int departureTimeIsBefore1,
               int departureTime1,
               int departureMaxDuration1,
               int departureTransportCompany1,
               int departureTransportType1,
               int departureTimeIsBefore2,
               int departureTime2,
               int departureMaxDuration2,
               int departureTransportCompany2,
               int departureTransportType2) {
  _main(departureTimeIsBefore1, departureTime1, departureMaxDuration1, departureTransportCompany1, departureTransportType1,
        departureTimeIsBefore2, departureTime2, departureMaxDuration2, departureTransportCompany2, departureTransportType2,
        departureTimeIsBefore2, departureTime2, departureMaxDuration2, departureTransportCompany2, departureTransportType2,
        departureTimeIsBefore1, departureTime1, departureMaxDuration1, departureTransportCompany1, departureTransportType1);
}

int compare(int o1_departureTimeIsBefore,
            int o1_departureTime,
            int o1_departureMaxDuration,
            int o1_departureTransportCompany,
            int o1_departureTransportType,
            int o2_departureTimeIsBefore,
            int o2_departureTime,
            int o2_departureMaxDuration,
            int o2_departureTransportCompany,
            int o2_departureTransportType) {

      int rv = 0;
      // Times
      // ---- rv = Int.compare(o1.departureTime, o2.departureTime);
      if (o1_departureTime < o2_departureTime) {
        rv = -1;
      } else if (o2_departureTime < o1_departureTime) {
        rv = 1;
      } else {
        rv = 0;
      }
      // ----
      if (rv == 0) {
          // Duration
          if (o1_departureMaxDuration < o2_departureMaxDuration) {
              rv = -1;
          }
          else if (o1_departureMaxDuration > o2_departureMaxDuration) {
              rv = 1;
          }
          else {
            // Transport company
            // ---- rv = Int.compare(o1.departureTransportCompany, o2.departureTransportCompany);
            if (o1_departureTransportCompany < o2_departureTransportCompany) {
              rv = -1;
            } else if (o2_departureTransportCompany < o1_departureTransportCompany) {
              rv = 1;
            } else {
              rv = 0;
            }
            // ----

            if (rv == 0) {
              // Transport type
              // ---- rv = Int.compare(o1.departureTransportType, o2.departureTransportType);
              if (o1_departureTransportType < o2_departureTransportType) {
                rv = -1;
              } else if (o2_departureTransportType < o1_departureTransportType) {
                rv = 1;
              } else {
                rv = 0;
              }
              // ----
            }
          }
      }
}
