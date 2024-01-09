/* @KESTREL
 * pre: for _i in (0..10) { left.a[_i] == right.a[_i] && left.b[_i] == right.b[_i] && left.c[_i] == right.c[_i] };
 * left: left;
 * right: right;
 * post: for _j in (0..10) { left.a[_j] == right.a[_j] && left.b[_j] == right.b[_j] && left.c[_j] == right.c[_j] };
 */
// TODO: Specs should be universally quantified over list size.

int read(int, int);
void store(int, int, int);

void left(int a, int b, int c, int size) {
  int i = 0;
  while (i < size) {
    store(a, i, read(a, i + 1));
    store(b, i, read(b, i) + read(a, i));
    store(c, i, read(c, i) + read(b, i));
    i = i + 1;
  }
}

void right(int a, int b, int c, int size) {
  int j = 0;
  store(a, 0, read(a, 0) + 1);
  store(b, 0, read(b, 0) + read(a, 0));
  store(a, 1, read(a, 1) + 1);

  while (j < size - 2) {
    store(a, j+2, read(a, j+2) + 1);
    store(b, j+1, read(b, j+1) + read(a, j+1));
    store(c, j, read(c, j) + read(b, j));
    j = j + 1;
  }
  store(c, j, read(c, j) + read(b, j));
  store(b, j+1, read(b, j+1) + read(a, j+1));
  store(c, j+1, read(c, j+1) + read(b, j+1));
}
