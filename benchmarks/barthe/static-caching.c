/* @KESTREL
 * pre: for _i in (0..24) { left.a[_i] == right.a[_i] }
     && for _i2 in (0..2) { left.s[_i2] == right.s[_i2] };
 * left: left;
 * right: right;
 * post: for _j in (0..6) { left.s[_j] == right.s[_j] };
 */

#define M 5
#define N 6
#define L 4

void _test_gen(int _arr1[N*L], int _arr2[N - M + 1]) {
  int _ai = 0;
  int l_a[N*L];
  int r_a[N*L];
  while (_ai < N*L) {
    l_a[_ai] = _arr1[_ai];
    r_a[_ai] = _arr1[_ai];
    _ai = _ai + 1;
  }

  int _si = 0;
  int l_s[N*L];
  int r_s[N*L];
  while (_si < N-M+1) {
    l_s[_si] = _arr2[_si];
    r_s[_si] = _arr2[_si];
    _si = _si + 1;
  }
}

void left(int a[N][L], int s[N-M+1]) {
  int i = 0;
  while (i < N - M) {
    s[i] = 0;
    int k = 0;
    while (k <= M - 1) {
      int l = 0;
      while (l <= L - 1) {
        s[i] = s[i] + a[i + k][l];
        l = l + 1;
      }
    }
  }
}

void right(int a[N][L], int s[N-M+1]) {
  s[0] = 0;
  int b[N];
  int k = 0;
  while (k <= M - 1) {
    b[k] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[k] = b[k] + a[k][l];
      l = l + 1;
    }
    s[0] = s[0] + b[k];
    k = k + 1;
  }
  int i = 1;
  while(i <= N - M) {
    b[i + M - 1] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[i+M-1] = b[i + M - 1] + a[i + M - 1][l];
      l = l + 1;
    }
    int z = b[i + M - 1] - b[i - 1];
    s[i] = s[i - 1] + z;
    i = i + 1;
  }
}
