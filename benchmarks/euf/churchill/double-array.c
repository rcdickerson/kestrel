/* @KESTREL
 * pre:   (forall i: int :: read(left.arr_in, i) == read(right.arr_in, i))
       && left.arr_in == right.arr_in
       && left.arr_size_in == right.arr_size_in
       && left.arr_size_in > 0
       && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
       && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * left:  left;
 * right: right;
 * post:  (forall i: int :: read(left.arr, i) == read(right.arr, i));
 */

int read(int arr_id, int index);
int store(int arr_id, int index, int value);
int f(int element);

void _test_gen(int arr, int size) {
  if (size < 0) size = size * - 1;
  size = size % 100;
  _main(arr, size, arr, size);
}

int left(int arr_in, int arr_size_in) {
  int arr = arr_in;
  int arr_size = arr_size_in;
  int i = 0;
  while (i < arr_size) {
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
    arr = store(arr, i + 1, read(arr, i));
    i = i + 2;
  }

}
