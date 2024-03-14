/* @KESTREL
 * pre: forall i: int ::
     (read(left.list_in, i) >= read(right.list_in, i) || read(right.list_in, i) - read(left.list_in, i) < epsilon) &&
     (read(left.list_in, i) <  read(right.list_in, i) || read(left.list_in, i) - read(right.list_in, i) < epsilon);
 * left: sort;
 * right: sort;
 * post: forall j: int ::
     (read(left.list_in, j) >= read(right.list_in, j) || read(right.list_in, j) - read(left.list_in, j) < epsilon) &&
     (read(left.list_in, j) <  read(right.list_in, j) || read(left.list_in, j) - read(right.list_in, j) < epsilon);
 */

const float epsilon = 0.01;

float read(int, int);
int store(int, int, float);

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
    int j = size - 1;
    while (j > i) {
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
