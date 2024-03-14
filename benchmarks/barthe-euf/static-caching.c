/* @KESTREL
 * pre: (forall i: int :: read(left.a, i) == read(right.a, i))
     && (forall i2: int :: read(left.s, i2) == read(right.s, i2));
 * left: left;
 * right: right;
 * post: forall j: int :: read(left.s, j) == read(right.s, j);
 */

int read(int, int);
int store(int, int, int);

void _test_gen(int a, int s, int lM, int lN, int lL, int rM, int rN, int rL) {
  if (lM < 0) { lM = lM * -1; } lM = lM % 10;
  if (lN < 0) { lN = lN * -1; } lN = lN % 10;
  if (lL < 0) { lL = lL * -1; } lL = lL % 10;
  if (rM < 0) { rM = rM * -1; } rM = rM % 10;
  if (rN < 0) { rN = rN * -1; } rN = rN % 10;
  if (rL < 0) { rL = rL * -1; } rL = rL % 10;
  if (lM < 2) { lM = lM + 5; }
  if (rM < 2) { rM = rM + 5; }
  if (lM > lN) { int tmp = lM;  lM = lN; lN = tmp; }
  if (rM > rN) { int tmp = rM;  rM = rN; rN = tmp; }
  _main(a, s, lM, lN, lL, a, s, rM, rN, rL);
}

void left(int a, int s, int M, int N, int L) {
  int i = 0;
  while (i < N - M) {
    s = store(s, i, 0);
    int k = 0;
    while (k <= M - 1) {
      int l = 0;
      while (l <= L - 1) {
        s = store(s, i, read(s, i) + read(read(a, i + k), l));
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
    b = store(b, k, 0);
    int l = 0;
    while (l <= L - 1) {
      b = store(b, k, read(b, k) + read(read(a, k), l));
      l = l + 1;
    }
    s = store(s, 0, read(s, 0) + read(b, k));
    k = k + 1;
  }
  int i = 1;
  while(i <= N - M) {
    b = store(b, i + M - 1, 0);
    int l = 0;
    while (l <= L - 1) {
      b = store(b, i+M-1, read(b, i + M - 1) + read(read(a, i + M - 1), l));
      l = l + 1;
    }
    int z = read(b, i + M - 1) - read(b, i - 1);
    s = store(s, i, read(s, i - 1) + z);
    i = i + 1;
  }
}
