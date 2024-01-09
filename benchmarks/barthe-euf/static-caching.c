/* @KESTREL
 * pre: for _i in (0..24) { left.a[_i] == right.a[_i] }
     && for _i2 in (0..2) { left.s[_i2] == right.s[_i2] };
 * left: left;
 * right: right;
 * post: for _j in (0..6) { left.s[_j] == right.s[_j] };
 */
// TODO: Specs should be universally quantified over list size.

int read(int, int);
void store(int, int, int);

void left(int a, int s, int M, int N, int L) {
  int i = 0;
  while (i < N - M) {
    store(s, i, 0);
    int k = 0;
    while (k <= M - 1) {
      int l = 0;
      while (l <= L - 1) {
        store(s, i, read(s, i) + read(read(a, i + k), l));
        l = l + 1;
      }
    }
  }
}

void right(int a, int s, int M, int N, int L) {
  store(s, 0, 0);
  int b = a + 1; // "new list"
  int k = 0;
  while (k <= M - 1) {
    store(b, k, 0);
    int l = 0;
    while (l <= L - 1) {
      store(b, k, read(b, k) + read(read(a, k), l));
      l = l + 1;
    }
    store(s, 0, read(s, 0) + read(b, k));
    k = k + 1;
  }
  int i = 1;
  while(i <= N - M) {
    store(b, i + M - 1, 0);
    int l = 0;
    while (l <= L - 1) {
      store(b, i+M-1, read(b, i + M - 1) + read(read(a, i + M - 1), l));
      l = l + 1;
    }
    int z = read(b, i + M - 1) - read(b, i - 1);
    store(s, i, read(s, i - 1) + z);
    i = i + 1;
  }
}
