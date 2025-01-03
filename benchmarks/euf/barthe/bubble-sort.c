/* @KESTREL
 * pre: left.size_in == right.size_in
     && (forall i: int, j: int, a: int, x: float :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: float :: (i != j) ==> read(store(a, i, x), j) == read(a, j))
     && (forall i: int ::
          (read(left.list_in, i) <  read(right.list_in, i) ==> read(right.list_in, i) - read(left.list_in, i) < epsilon) &&
          (read(left.list_in, i) >= read(right.list_in, i) ==> read(left.list_in, i) - read(right.list_in, i) < epsilon));
 * left: sort;
 * right: sort;
 * post: forall j: int ::
     (read(left.list, j) <  read(right.list, j) ==> read(right.list, j) - read(left.list, j) < epsilon) &&
     (read(left.list, j) >= read(right.list, j) ==> read(left.list, j) - read(right.list, j) < epsilon);
 */

const float epsilon = 0.01;

float read(int list_id, int index);
int store(int list_id, int index, float value);

void _test_gen(int list_id, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(list_id, size, list_id, size);
}

void sort(int list_in, int size_in) {
  int list = list_in;
  int size = size_in;
  int i = 0;
  while (i < size) {
    _invariant("forall j: int :: (read(left.list, j) <  read(right.list, j) ==> read(right.list, j) - read(left.list, j) < epsilon) && (read(left.list, j) >= read(right.list, j) ==> read(left.list, j) - read(right.list, j) < epsilon)");
    int j = size - 1;
    while (j > i) {
      _invariant("forall j: int :: (read(left.list, j) <  read(right.list, j) ==> read(right.list, j) - read(left.list, j) < epsilon) && (read(left.list, j) >= read(right.list, j) ==> read(left.list, j) - read(right.list, j) < epsilon)");
      float prev = read(list, j - 1);
      float cur  = read(list, j);
      if (prev > cur) {
        float val = read(list, j);
        float prev_val = read(list, j-1);
        list = store(list, j, prev_val);
        list = store(list, j - 1, val);
      }
      j = j - 1;
    }
    i = i + 1;
  }
}
