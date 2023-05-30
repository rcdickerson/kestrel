/* @KESTREL
 * pre: for _i in 1..o1_length { left.o1[_i] == right.o2[_i] } &&
        for _j in 1..o2_length { left.o2[_j] == right.o1[_j] } &&
        left.o1_length == right.o2_length &&
        right.o2_length == left.o1_length;
 * left: cmp;
 * right: cmp;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/23907134/comparing-two-arrays-using-dictionary-order-in-an-array-of-arrays-java
 *
 */

void left(int o1_length, int o2_length, int o1[o1_length], int o2[o2_length]) {
  int ret = -999;

  int index;
  int aentry;
  int bentry;

  index = 0;

  while ((index < o1_length) && (index < o2_length)) {
    aentry = o1[index];
    bentry = o2[index];
    if (aentry < bentry) {
      ret = -1;
      break;
    }
    if (aentry > bentry) {
      ret = 1;
      break;
    }
    index++;
  }

  if (ret == -999) {
    if (o1_length < o2_length) {
      ret = -1;
    }
    if (o1_length > o2_length) {
      ret = 1;
    }
    ret = 0;
  }
}
