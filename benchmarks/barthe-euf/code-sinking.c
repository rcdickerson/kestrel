/* @KESTREL
 * pre: for p_i in (0..11) { left.a[p_i] == right.a[p_i] };
 * left: left;
 * right: right;
 * post: for p_j in (0..11) { left.a[p_j] == right.a[p_j] };
 */
// TODO: Specs should be universally quantified over list size.

int read(int, int);
void store(int, int, int);

void left(int a, int size) {
  int max = read(a, 0);
  int maxi = 0;
  int i = 0;
  while (i < size) {
    if (max < read(a, i)) {
      max = read(a, i);
      maxi = i;
    }
    i = i + 1;
  }
  int t = read(a, size);
  store(a, size, max);
  store(a, maxi, t);
}

void right(int a, int size) {
  int j = 0;
  int max;
  int maxi;
  while (j < size) {
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
      store(a, size, max);
      store(a, maxi, t);
    }
    j = j + 1;
  }
}
