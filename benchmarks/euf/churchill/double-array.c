/* @KESTREL
 * pre: left.arr_in == right.arr_in
     && left.arr_size_in == right.arr_size_in
     && left.arr_size_in > 0
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * left:  left;
 * right: right;
 * post:  left.arr == right.arr;
 */

// post:  (forall i: int :: read(left.arr, i) == read(right.arr, i)) && left.arr == right.arr;

int read(int arr_id, int index);
int store(int arr_id, int index, int value);
int f(int element);

void _test_gen(int arr, int size) {
  if (size < 0) size = size * - 1;
  size = size % 100;
  if (size == 0) { size = 1; }
  _main(arr, size, arr, size);
}

int left(int arr_in, int arr_size_in) {
  int arr = arr_in;
  int arr_size = arr_size_in;
  int i = 0;
  while (i < arr_size) {
//    _invariant("forall i: int :: read(left.arr, i) == read(right.arr, i)");
    _invariant("r_arr_size % 2 == r_i % 2");
    _invariant("l_i < l_arr_size ==> l_i + 1 < l_arr_size");
    _invariant("l_i == r_i");
    _invariant("l_arr == r_arr");
    arr = store(arr, i, read(arr, i));
    i = i + 1;
  }
}

int right(int arr_in, int arr_size_in) {
  int arr = arr_in;
  int arr_size = arr_size_in;
  int i = 0;
  if (arr_size % 2 == 1) {
    arr = store(arr, i, read(arr, i));
    i = i + 1;
  }
  while (i < arr_size) {
    arr = store(arr, i, read(arr, i));
    arr = store(arr, i + 1, read(arr, i + 1));
    i = i + 2;
  }

}
