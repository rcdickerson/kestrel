/* @KESTREL
 * pre: for p_i in (0..20) { left.a[p_i] == right.a[p_i] && left.b[0] == right.b[0] };
 * left: left;
 * right: right;
 * post: for p_j in (1..20) { left.d[p_j] == right.d[p_j] };
 */
// TODO: Specs should be universally quantified over list size.

int read(int, int);
int store(int, int, int);

void left(int a, int b, int size) {
  int i = 1;
  int d = a + b + 1; // "New list"
  while (i <= size) {
    store(b, i, read(a, i));
    store(d, i, read(b, i - 1));
    i = i + 1;
  }
}

void right(int a, int b, int size) {
  int j = 1;
  int d = a + b + 1; // "New list"
  store(d, 1, read(b, 0));
  while (j <= size - 1) {
    store(b, j, read(a, j));
    store(d, j+1, read(b, j));
    j = j + 1;
  }
  store(b, size, read(a, size));
}
