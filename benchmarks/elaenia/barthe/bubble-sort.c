/* @ELAENIA
 * pre: left.size == right.size
     && left.size >= 1
     && left.list == right.list;
 * pre_sketch: left.size <= 4;
 * forall: sort;
 * exists: sort;
 * post: forall j: int ::
     (left.list[j] < right.list[j] ==> right.list[j] - left.list[j] < epsilon) &&
     (left.list[j] >= right.list[j] ==> left.list[j] - right.list[j] < epsilon);
 */

float epsilon = 0.01;

void _test_gen(int size,
               int a0, int a1, int a2, int a3) {
  if (size < 0) { size = size * -1; }
  size = size % 100;

  int list[size] = {0};
  if (size > 0) { list[0] = a0; }
  if (size > 1) { list[1] = a1; }
  if (size > 2) { list[2] = a2; }
  if (size > 3) { list[3] = a3; }

  _main(size, list, size, list);
}

void sort(int size, float list[size]) {
  int i = 0;
  while (i < size) {
    int j = size - 1;
    while (j > i) {
      float prev = list[j - 1];
      float cur  = list[j];
      if (prev > cur) {
        float val = list[j];
        float prev_val = list[j-1];
        list[j] = prev_val;
        list[j - 1] = val;
      }
      j = j - 1;
    }
    i = i + 1;
  }
}
