/* @KESTREL
 * pre: left.o1_null          == right.o2_null &&
        left.o1_fileName_null == right.o2_fileName_null &&
        left.o1_fileName      == right.o2_fileName &&
        left.o2_null          == right.o1_null &&
        left.o2_fileName_null == right.o1_fileName_null &&
        left.o2_fileName      == right.o1_fileName;
 * left: cmp;
 * right: cmp;
 * post: left.result == -1 * right.result;
 */

void cmp (int o1_null,
          int o2_null,
          int o1_fileName_null,
          int o2_fileName_null,
          int o1_fileName,
          int o2_fileName) {
  int result = -999;

  if (o1_null){
    if (o2_null){
      result = 0;
    } else {
      result = 1;
    }
  } else if (o2_null) {
    result = -1;
  }

  if (result == -999) {
    int n1 = o1_fileName;
    int n2 = o2_fileName;

    if (o1_fileName_null) {
      if (o2_fileName_null) {
        result = 0;
      } else {
        result = 1;
      }
    } else if (o2_fileName_null) {
      result = -1;
    }
    result = n1 - n2;
  }
}
