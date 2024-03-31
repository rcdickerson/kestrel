/* @KESTREL
 * pre: left.val_in > 0
     && right.val_in > 0
     && left.len_in >= 0
     && right.len_in >= 0
     && left.len_in == right.len_in
     && (forall i: int :: read(left.arr_in, i) == read(right.arr_in, i))
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * left: left;
 * right: right;
 * post: left.i == right.j;
 */

int read(int arr, int index);
int store(int arr, int index, int value);
int shift(int arr, int idx, int amt);

void _test_gen(int a_left, int a_right, int len, int val_left, int val_right) {
  if (len < 0) { len = len * -1; }
  len = (len % 100) + 1;

  if (val_left < 0) { val_left = val_left * -1; }
  val_left = (val_left % 100) + 1;

  if (val_right < 0) { val_right = val_right * -1; }
  val_right = (val_right % 100) + 1;

  _main(a_left, len, val_left, a_right, len, val_right);
}

void left(int arr_in, int len_in, int val_in) {
  int arr = arr_in;
  int len = len_in;
  int val = val_in;
  int i = 0;
  while (i < len && read(arr, i) < val) {
    _invariant("left.i <= left.len");
    i = i + 1;
  }
  arr = shift(arr, i, 1);
  len = len + 1; // spec of shiftArray
  arr = store(arr, i, val);
  while (i < len) {
    _invariant("left.i <= left.len");
    i = i + 1;
  }
}

void right(int arr_in, int len_in, int val_in) {
  int arr = arr_in;
  int len = len_in;
  int val = val_in;
  int j = 0;
  while (j < len && read(arr, j) < val) {
    _invariant("right.j <= right.len");
    j = j + 1;
  }
  arr = shift(arr, j, 1);
  len = len + 1; // spec of shiftArray
  arr = store(arr, j, val);
  while (j < len) {
    _invariant("right.j <= right.len");
    j = j + 1;
  }
}
