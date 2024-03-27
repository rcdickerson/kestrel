/* @KESTREL
 * pre: left.a_in == right.a_in
     && left.b_in == right.b_in
     && left.size_in == right.size_in
     && 1 <= left.size_in;
 * left: left;
 * right: right;
 * post: left.d == right.d;
 */

int read(int list_id, int index);
int store(int list_id, int index, int value);

// assume(forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x);
// assume(forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));

void _test_gen(int a, int b, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(a, b, size, a, b, size);
}

void left(int a_in, int b_in, int size_in) {
  int a = a_in;
  int b = b_in;
  int size = size_in;
  int i = 1;
  int d = a + b + 1; // "New list"
  while (i <= size) {
    b = store(b, i, read(a, i));
    d = store(d, i, read(b, i - 1));
    i = i + 1;
  }
}

void right(int a_in, int b_in, int size_in) {
  int a = a_in;
  int b = b_in;
  int size = size_in;
  int j = 1;
  int d = a + b + 1; // "New list"
  d = store(d, 1, read(b, 0));
  while (j <= size - 1) {
    b = store(b, j, read(a, j));
    d = store(d, j+1, read(b, j));
    j = j + 1;
  }
  b = store(b, size, read(a, size));
}
