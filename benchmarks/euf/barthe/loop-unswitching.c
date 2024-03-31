/* @KESTREL
 * pre: left.k_in == right.k_in
     && left.x_in == right.x_in
     && left.a_in == right.a_in
     && left.b_in == right.b_in
     && left.c_in == right.c_in
     && left.size == right.size
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * left: left;
 * right: right;
 * post: (forall i: int :: (read(left.a, i) == read(right.a, i)))
      && (forall i: int :: (read(left.b, i) == read(right.b, i)))
      && (forall i: int :: (read(left.c, i) == read(right.c, i)));
 */

int read(int list_id, int index);
int store(int list_id, int index, int value);

void _test_gen(int a, int b, int c, int k, int x, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;

  int l_size = size;
  int r_size = size;
  int l_a = a;
  int r_a = a;
  int l_b = b;
  int r_b = b;
  int l_c = c;
  int r_c = c;
  int l_k = k;
  int r_k = k;
  int l_x = x;
  int r_x = x;

  _main(a, b, c, k, x, size, a, b, c, k, x, size);
}

void left(int a_in, int b_in, int c_in, int k_in, int x_in, int size) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int k = k_in;
  int x = x_in;

  int i = 0;
  while (i < size) {
    _invariant("forall i: int :: (read(left.a, i) == read(right.a, i))");
    _invariant("forall i: int :: (read(left.b, i) == read(right.b, i))");
    _invariant("forall i: int :: (read(left.c, i) == read(right.c, i))");
    a = store(a, i, read(a, i) + k);
    if (x < 7) {
      b = store(b, i, read(a, i) * read(c, i));
    } else {
      b = store(b, i, read(a, i-1) * read(b, i-1));
    }
    i = i + 1;
  }
}

void right(int a_in, int b_in, int c_in, int k_in, int x_in, int size) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int k = k_in;
  int x = x_in;

  if (x < 7) {
    int j = 0;
    while (j < size) {
      a = store(a, j, read(a, j) + k);
      b = store(b, j, read(a, j) * read(c, j));
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < size) {
      a = store(a, j, read(a, j) + k);
      b = store(b, j, read(a, j-1) * read(b, j-1));
      j = j + 1;
    }
  }
}
