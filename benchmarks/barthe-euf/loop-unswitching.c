/* @KESTREL
 * pre: left.k == right.k && left.x == right.x &&
        for p_i in (0..10) { left.a[p_i] == right.a[p_i] && left.b[p_i] == right.b[p_i] && left.c[p_i] == right.c[p_i]};
 * left: left;
 * right: right;
 * post: for p_j in (0..10) { left.a[p_j] == right.a[p_j] && left.b[p_j] == right.b[p_j] && left.c[p_j] == right.c[p_j] };
 */
// TODO: Specs should be universally quantified over list size.

int read(int, int);
void store(int, int, int);

void left(int a, int b, int c, int k, int x, int size) {
  int i = 0;
  while (i < size) {
    store(a, i, read(a, i) + k);
    if (x < 7) {
      store(b, i, read(a, i) * read(c, i));
    } else {
      store(b, i, read(a, i - 1) * read(b, i - 1));
    }
    i = i + 1;
  }
}

void right(int a, int b, int c, int k, int x, int size) {
  if (x < 7) {
    int j = 0;
    while (j < size) {
      store(a, j, read(a, j) + k);
      store(b, j, read(a, j) * read(c, j));
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < size) {
      store(a, j, read(a, j) + k);
      store(b, j, read(a, j - 1) * read(b, j - 1));
      j = j + 1;
    }
  }
}
