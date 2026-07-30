#define N 20

void _test_gen(int _arr[N], int _b) {
  int _ai = 0;
  int l_a[N + 1];
  int l_b[N + 1];
  int r_a[N + 1];
  int r_b[N + 1];

  while (_ai < N) {
    l_a[_ai] = _arr[_ai];
    r_a[_ai] = _arr[_ai];
    _ai = _ai + 1;
  }
  l_b[0] = _b;
  r_b[0] = _b;
}

void left(int a[N+1], int b[N+1]) {
  int i = 1;
  int d[N+1];
  while (i <= N ) {
    b[i] = a[i];
    d[i] = b[i - 1];
    i = i + 1;
  }
}