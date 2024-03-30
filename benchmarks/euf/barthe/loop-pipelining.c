/* @KESTREL
 * pre: (forall i: int :: read(l_a_in, i) == read(r_a_in, i))
     && (forall i: int :: read(l_b_in, i) == read(r_b_in, i))
     && (forall i: int :: read(l_c_in, i) == read(r_c_in, i))
     && left.size_in == right.size_in
     && 2 <= left.size_in
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * left: left;
 * right: right;
 * post: (forall i: int :: read(l_a, i) == read(r_a, i))
      && (forall i: int :: read(l_b, i) == read(r_b, i))
      && (forall i: int :: read(l_c, i) == read(r_c, i));
 */

void _test_gen(int a, int b, int c, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(a, b, c, size, a, b, c, size);
}

int read(int list_id, int index);
int store(int list_id, int index, int value);

void left(int a_in, int b_in, int c_in, int size_in) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int size = size_in;

  int i = 0;
  while (i < size) {
    _invariant("forall i: int :: read(l_a, i) == read(r_a, i)");
    _invariant("read(l_b, r_j + 1) == read(r_b, r_j + 1) + read(l_a, r_j + 1)");
    _invariant("forall i: int :: (i != r_j + 1) ==> read(l_b, i) == read(r_b, i)");
    _invariant("read(l_c, r_j) == read(r_c, r_j) + read(l_b, r_j)");
    _invariant("read(l_c, r_j + 1) == read(r_c, r_j + 1) + read(l_b, r_j + 1)");
    _invariant("forall i: int :: (i != r_j && i != r_j + 1) ==> read(l_c, i) == read(r_c, i)");
    _invariant("l_i == r_j + 2");
    a = store(a, i, read(a, i) + 1);
    b = store(b, i, read(b, i) + read(a, i));
    c = store(c, i, read(c, i) + read(b, i));
    i = i + 1;
  }
}

void right(int a_in, int b_in, int c_in, int size_in) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int size = size_in;

  int j = 0;
  a = store(a, 0, read(a, 0) + 1);
  b = store(b, 0, read(b, 0) + read(a, 0));
  a = store(a, 1, read(a, 1) + 1);

  while (j < size - 2) {
    a = store(a, j+2, read(a, j + 2) + 1);
    b = store(b, j+1, read(b, j + 1) + read(a, j + 1));
    c = store(c, j, read(c, j) + read(b, j));
    j = j + 1;
  }
  c = store(c, j,  read(c, j) + read(b, j));
  b = store(b, j + 1, read(b, j + 1) + read(a, j + 1));
  c = store(c, j + 1, read(c, j + 1) + read(b, j + 1));
}
