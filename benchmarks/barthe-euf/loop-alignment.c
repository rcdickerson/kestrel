/* @KESTREL
 * pre: forall i: int :: read(left.a_in, i) == read(right.a_in, i) && read(left.b_in, 0) == read(right.b_in, 0);
 * left: left;
 * right: right;
 * post: forall j: int :: read(left.d, j) == read(right.d, j);
 */

int read(int, int);
int store(int, int, int);

void _test_gen(int a, int b, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(a, b, size, a, b, size);
}

void left(int a_in, int b_in, int size) {
  int a = a_in;
  int b = b_in;
  int i = 1;
  int d = a + b + 1; // "New list"
  while (i <= size) {
    b = store(b, i, read(a, i));
    d = store(d, i, read(b, i - 1));
    i = i + 1;
  }
}

void right(int a_in, int b_in, int size) {
  int a = a_in;
  int b = b_in;
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
