/* @KESTREL
 * pre: for _i in (1..left_o1_length) { left_o1[_i] == right_o2[_i] } &&
        for _j in (1..left_o2_length) { left_o2[_j] == right_o1[_j] };
 * left: left;
 * right: right;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/23907134/comparing-two-arrays-using-dictionary-order-in-an-array-of-arrays-java
 *
 */

const int left_o1_length = 10;
const int left_o2_length = 15;
int left_o1[left_o1_length];
int left_o2[left_o2_length];

const int right_o1_length = 15;
const int right_o2_length = 10;
int right_o1[right_o1_length];
int right_o2[right_o2_length];

void _generator(int _arr1[left_o1_length], int _arr2[left_o2_length]) {
  int _ai1 = 0;
  while (_ai1 < left_o1_length) {
    left_o1[_ai1] = _arr1[_ai1];
    right_o2[_ai1] = _arr1[_ai1];
    _ai1 = _ai1 + 1;
  }
  int _ai2 = 0;
  while (_ai2 < left_o2_length) {
    left_o2[_ai2] = _arr2[_ai2];
    right_o1[_ai2] = _arr2[_ai2];
    _ai2 = _ai2 + 1;
  }
}

void left(void) {
  int ret = -999;

  int index;
  int aentry;
  int bentry;

  index = 0;

  while ((index < left_o1_length) && (index < left_o2_length)) {
    aentry = left_o1[index];
    bentry = left_o2[index];
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
    if (left_o1_length < left_o2_length) {
      ret = -1;
    }
    if (left_o1_length > left_o2_length) {
      ret = 1;
    }
    ret = 0;
  }
}

void right(void) {
  int ret = -999;

  int index;
  int aentry;
  int bentry;

  index = 0;

  while ((index < right_o1_length) && (index < right_o2_length)) {
    aentry = right_o1[index];
    bentry = right_o2[index];
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
    if (right_o1_length < right_o2_length) {
      ret = -1;
    }
    if (right_o1_length > right_o2_length) {
      ret = 1;
    }
    ret = 0;
  }
}
