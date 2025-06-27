/* @ELAENIA
 * pre: left.size == right.size
     && left.size > 0
     && left.a =a= right.a;
 * pre_sketch: left.size <= 4;
 * forall: left;
 * exists: right;
 * post: left.a =a= right.a;
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
    _invariant("l_i == r_j");
    _invariant("0 <= l_i && l_i <= l_size + 1");
    _invariant("0 <= r_j && r_j <= r_size + 1");
    _invariant("0 <= l_maxi && l_maxi <= l_i && l_maxi <= l_size");
    _invariant("0 <= r_maxi && r_maxi <= r_j && r_maxi <= r_size");
    _invariant("(0 < r_j && r_j <= r_size) ==> r_max == r_a[r_maxi]");
    _invariant("l_max == l_a[l_maxi]");
    _invariant("r_j == r_size + 1 ==> l_max == r_a[r_size]");
    _invariant("r_j == r_size + 1 ==> l_a[l_maxi] == r_a[r_size]");
    _invariant("l_maxi == r_maxi");
    _invariant("r_j == r_size + 1 ==> forall i: int :: (i >= 0 && i <= l_size && i != r_maxi && i != r_size) ==> (l_a[i] == r_a[i])");
    _invariant("r_j <= r_size ==> l_a =a= r_a");
    _invariant("l_i > 0 ==> l_max == r_max");
    _invariant("r_j == r_size + 1 ==> l_a[l_size] == r_a[r_maxi]");
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
  int t = 0;
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
      t = a[size];
      a[size] = max;
      a[maxi] = t;
    }
    j = j + 1;
  }
}
