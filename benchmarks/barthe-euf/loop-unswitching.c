/* @KESTREL
 * pre: left.k == right.k && left.x == right.x &&
        for _i in (0..10) { left.a[_i] == right.a[_i] && left.b[_i] == right.b[_i] && left.c[_i] == right.c[_i]};
 * left: left;
 * right: right;
 * post: for _j in (0..10) { left.a[_j] == right.a[_j] && left.b[_j] == right.b[_j] && left.c[_j] == right.c[_j] };
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
