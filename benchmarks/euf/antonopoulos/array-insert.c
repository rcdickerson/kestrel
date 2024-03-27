/* @KESTREL
 * pre: left.val_in > 0 && right.val_in > 0;
 * left: left;
 * right: right;
 * post: left.i == right.j;
 */

int read(int array, int index);
int store(int array, int index, int value);
int shift(int array, int idx, int amt);

void _test_gen(int a_left, int a_right, int len_left, int len_right, int val_left, int val_right) {
  if (val_left < 0) { val_left = val_left * -1; } val_left = val_left + 1;
  if (val_right < 0) { val_right = val_right * -1; } val_right = val_right + 1;
  _main(a_left, len_left, val_left, a_right, len_right, val_right);
}

void left(int arr_in, int len_in, int val_in) {
  int arr = arr_in;
  int len = len_in;
  int val = val_in;
  int i = 0;
  while( i < len && read(arr, i) < val) {
    i = i + 1;
  }
  arr = shift(arr, i, 1);
  len = len + 1; // spec of shiftArray
  arr = store(arr, i, val);
  while (i < len) {
    i = i + 1;
  }
}

void right(int arr_in, int len_in, int val_in) {
  int arr = arr_in;
  int len = len_in;
  int val = val_in;
  int j = 0;
  while( j < len && read(arr, j) < val) {
    j = j + 1;
  }
  arr = shift(arr, j, 1);
  len = len + 1; // spec of shiftArray
  arr = store(arr, j, val);
  while (j < len) {
    j = j + 1;
  }
}
