/* @KESTREL
 * pre: left.a_in == right.a_in
     && left.M_in == right.M_in
     && left.N_in == right.N_in
     && left.L_in == right.L_in
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * left: left;
 * right: right;
 * post: left.s == right.s;
 */

int read(int list_id, int index);
int store(int list_id, int index, int value);

void _test_gen(int a, int M, int N, int L) {
  if (M < 0) { M = M * -1; } M = M % 10;
  if (N < 0) { N = N * -1; } N = N % 10;
  if (L < 0) { L = L * -1; } L = L % 10;

  int l_a_in = a;
  int l_M_in = M;
  int l_N_in = N;
  int l_L_in = L;

  int r_a_in = a;
  int r_M_in = M;
  int r_N_in = N;
  int r_L_in = L;

  _main(a, M, N, L, a, M, N, L);
}

void left(int a_in, int M_in, int N_in, int L_in) {
  int a = a_in;
  int M = M_in;
  int N = N_in;
  int L = L_in;
  int s = 0;
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
      k = k + 1;
    }
    i = i + 1;
  }
}

void right(int a_in, int M_in, int N_in, int L_in) {
  int a = a_in;
  int M = M_in;
  int N = N_in;
  int L = L_in;
  int s = 0;
  int b = 1;

  s = store(s, 0, 0);
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
      b = store(b, i + M - 1, read(b, i + M - 1) + read(read(a, i + M - 1), l));
      l = l + 1;
    }
    int z = read(b, i + M - 1) - read(b, i - 1);
    s = store(s, i, read(s, i - 1) + z);
    i = i + 1;
  }
}
