/* @KESTREL
 * pre: (forall i: int :: left.a[i] == right.a[i])
     && (forall i2: int :: left.s[i2] == right.s[i2]);
 * left: left;
 * right: right;
 * post: forall j: int :: left.s[j] == right.s[j];
 */

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
