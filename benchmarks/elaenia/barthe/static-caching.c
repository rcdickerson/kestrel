/* @ELAENIA
 * pre: left.M == right.M
     && left.N == right.N
     && left.L == right.L
     && left.M > 0
     && left.N > 0
     && left.L > 0
     && left.N > left.M
     && left.a == right.a;
 * pre_sketch: left.M <= 2
            && left.N <= 2
            && left.L <= 2;
 * forall: left;
 * exists: right;
 * post: left.s == right.t;
 */

void _test_gen(int M, int N, int L) {
  if (M < 0) { M = M * -1; } M = M % 10;
  if (N < 0) { N = N * -1; } N = N % 10;
  if (L < 0) { L = L * -1; } L = L % 10;

  if (M > N) {
    int temp = M;
    M = N;
    N = temp;
  }

  int a[N][L] = {{0}};

  _main(M, N, L, a, M, N, L, a);
}

void left(int M, int N, int L, int a[N][L]) {
  int s[(N-M)+1] = {0};
  int i = 0;

  while (i <= N - M) {
    s[i] = 0;
    int k = 0;
    while (k <= M - 1) {
      int l = 0;
      while (l <= L - 1) {
        s[i] = s[i] + a[i+k][l];
        l = l + 1;
      }
      k = k + 1;
    }
    i = i + 1;
  }
}

void right(int M, int N, int L, int a[N][L]) {
  int t[(N-M)+1] = {0};
  int b[N] = {0};

  t[0] = 0;
  int k = 0;
  while (k <= M - 1) {
    b[k] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[k] = b[k] + a[k][l];
      l = l + 1;
    }
    t[0] = t[0] + b[k];
    k = k + 1;
  }
  int i = 1;
  while(i <= N - M) {
    b[i+M-1] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[i+M-1] = b[i+M-1] + a[i+M-1][l];
      l = l + 1;
    }
    int z = b[i+M-1] - b[i-1];
    t[i] = t[i-1] + z;
    i = i + 1;
  }
}
