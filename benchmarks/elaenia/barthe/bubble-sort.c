/* @ELAENIA
 * pre: left.size == right.size
     && left.size >= 1
     && left.list == right.list;
 * pre_sketch: left.size <= 3;
 * forall: sort;
 * exists: sort;
 * post: left.list == right.list;
 * aspecs:
 *   compare(i, j) {
 *     pre: true;
 *     post: (i <  j ==> ret! < 10)
 *        && (i == j ==> ret! == 10)
 *        && (i >  j ==> ret! > 10);
 *   }
 * especs:
 *   compare(i, j) {
 *     choiceVars: n;
 *     pre: n == 9 || n == 10 || n == 11;
 *     post: ret! == n;
 *   }
 */

int compare(int i, int j);

void _test_gen(int size,
               int a0, int a1, int a2, int a3) {
  if (size < 0) { size = size * -1; }
  size = size % 10;

  int list[size] = {0};
  if (size > 0) { list[0] = a0; }
  if (size > 1) { list[1] = a1; }
  if (size > 2) { list[2] = a2; }
  if (size > 3) { list[3] = a3; }

  _main(size, list, size, list);
}

void sort(int size, int list[size]) {
  int i = 0;
  int j = 0;
  while (i < size) {
    j = size - 1;
    while (j > i) {
      _invariant("l_j < l_size");
      int cmp;
      cmp = compare(list[j - 1], list[j]);
      if (cmp > 10) {
        int val = list[j];
        int prev_val = list[j-1];
        list[j] = prev_val;
        list[j - 1] = val;
      }
      j = j - 1;
    }
    i = i + 1;
  }
}
