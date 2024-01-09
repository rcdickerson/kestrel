/* @KESTREL
 * pre: for _i in (0..11) { left.a[_i] == right.a[_i] };
 * left: left;
 * right: right;
 * post: for _j in (0..11) { left.a[_j] == right.a[_j] };
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
