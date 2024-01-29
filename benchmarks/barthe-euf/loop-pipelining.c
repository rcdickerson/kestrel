/* @KESTREL
 * pre: for p_i in (0..10) { left.a[p_i] == right.a[p_i] && left.b[p_i] == right.b[p_i] && left.c[p_i] == right.c[p_i] };
 * left: left;
 * right: right;
 * post: for p_j in (0..10) { left.a[p_j] == right.a[p_j] && left.b[p_j] == right.b[p_j] && left.c[p_j] == right.c[p_j] };
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
