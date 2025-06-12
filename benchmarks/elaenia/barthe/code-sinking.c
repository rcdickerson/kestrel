/* @ELAENIA
 * pre: left.size == right.size
     && left.size > 0
     && left.a == right.a;
 * pre_sketch: left.size <= 4;
 * forall: left;
 * exists: right;
 * post: left.a == right.a;
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
  size = (size % 10) + 1;

  int list[size+1] = {0};
  if (size > 0) { list[0] = a0; }
  if (size > 1) { list[1] = a1; }
  if (size > 2) { list[2] = a2; }
  if (size > 3) { list[3] = a3; }

  _main(size, list, size, list);
}

void left(int size, int a[size+1]) {
  int max = a[0];
  int maxi = 0;
  int i = 0;
  while (i <= size) {
    int cmp;
    cmp = compare(max, a[i]);
    if (cmp < 10) {
      max = a[i];
      maxi = i;
    }
    i = i + 1;
  }
  int t = a[size];
  a[size] = max;
  a[maxi] = t;
}

void right(int size, int a[size+1]) {
  int j = 0;
  int max = 0;
  int maxi = 0;
  while (j <= size) {
    if (j == 0) {
      max = a[0];
      maxi = 0;
    }
    int cmp;
    cmp = compare(max, a[j]);
    if (cmp < 10) {
      max = a[j];
      maxi = j;
    }
    if (j == size) {
      int t = a[size];
      a[size] = max;
      a[maxi] = t;
    }
    j = j + 1;
  }
}
