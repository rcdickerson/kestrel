/* @KESTREL
 * pre: left.o1_in == right.o2_in
     && left.len1_in == right.len2_in
     && left.o2_in == right.o1_in
     && left.len2_in == right.len1_in
     && left.len1_in >= 0
     && left.len2_in >= 0;
 * left: compare;
 * right: compare;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/23907134/comparing-two-arrays-using-dictionary-order-in-an-array-of-arrays-java
 *
 */

int read(int arr, int index);
int store(int arr, int index, int value);

void _test_gen(int arr1, int len1, int arr2, int len2) {
  if (len1 < 0) { len1 = len1 * -1; } len1 = len1 % 100;
  if (len2 < 0) { len2 = len2 * -1; } len2 = len2 % 100;
  _main(arr1, len1, arr2, len2, arr2, len2, arr1, len1);
}

void compare(int o1_in, int len1_in, int o2_in, int len2_in) {
  int o1 = o1_in;
  int len1 = len1_in;
  int o2 = o2_in;
  int len2 = len2_in;

  int ret = -999;

  int index;
  int aentry;
  int bentry;

  index = 0;

  while ((index < len1) && (index < len2)) {
    aentry = read(o1, index);
    bentry = read(o2, index);
    if (aentry < bentry) {
      ret = -1;
      break;
    }
    if (aentry > bentry) {
      ret = 1;
      break;
    }
    index = index + 1;
  }

  if (ret == -999) {
    if (len1 < len2) {
      ret = -1;
    }
    if (len1 > len2) {
      ret = 1;
    }
    ret = 0;
  }
}
