/* @KESTREL
 * pre: (forall i: int :: read(left.a_in, i) == read(right.a_in, i))
     && left.size == right.size
     && left.size > 0
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * left: left;
 * right: right;
 * post: (forall i: int :: read(left.a, i) == read(right.a, i));
 */

int read(int list_id, int index);
int store(int list_id, int index, int value);

void _test_gen(int list_id, int size) {
  if (size < 0) { size = size * -1; }
  size = (size % 100) + 1;
  _main(list_id, size, list_id, size);
}

void left(int a_in, int size) {
  int a = a_in;
  int max = read(a, 0);
  int maxi = 0;
  int i = 0;
  while (i <= size) {
    _invariant("r_j <= r_size ==> forall i: int :: read(l_a, i) == read(r_a, i)");
    _invariant("0 <= l_i && l_i <= l_size + 1");
    _invariant("0 <= r_j && r_j <= r_size + 1");
    _invariant("l_i == r_j");
    _invariant("0 <= l_maxi && l_maxi <= l_i");
    _invariant("0 <= r_maxi && r_maxi <= r_j");
    _invariant("0 <= l_maxi <= l_size");
    _invariant("0 <= r_maxi <= r_size");
    _invariant("l_i > 0 ==> l_max == r_max");
    _invariant("l_maxi == r_maxi");
    _invariant("0 < l_i ==> l_max == r_max");
    _invariant("l_max == read(l_a, l_maxi)");
    _invariant("0 < r_j && r_j <= r_size ==> r_max == read(r_a, r_maxi)");
    _invariant("r_j == r_size + 1 ==> forall i: int :: (i != r_maxi && i != r_size) ==> (read(l_a, i) == read(r_a, i))");
    _invariant("r_j == r_size + 1 ==> l_max == read(r_a, r_size)");
    _invariant("r_j == r_size + 1 ==> read(l_a, l_maxi) == read(r_a, r_size)");
    _invariant("r_j == r_size + 1 ==> read(l_a, l_size) == read(r_a, r_maxi)");
    if (max < read(a, i)) {
      max = read(a, i);
      maxi = i;
    }
    i = i + 1;
  }
  int t = read(a, size);
  a = store(a, size, max);
  a = store(a, maxi, t);
}

void right(int a_in, int size) {
  int a = a_in;
  int j = 0;
  int max = 0;
  int maxi = 0;
  while (j <= size) {
    if (j == 0) {
      max = read(a, 0);
      maxi = 0;
    }
    if (max < read(a, j)) {
      max = read(a, j);
      maxi = j;
    }
    if (j == size) {
      int t = read(a, size);
      a = store(a, size, max);
      a = store(a, maxi, t);
    }
    j = j + 1;
  }
}
