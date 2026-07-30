#define N 10

void _test_gen(int _arr1[N], int _arr2[N], int _arr3[N]) {
  int _ai = 0;
  int l_a[N];
  int l_b[N];
  int l_c[N];
  int r_a[N];
  int r_b[N];
  int r_c[N];
  while (_ai < N) {
    l_a[_ai] = _arr1[_ai];
    r_a[_ai] = _arr1[_ai];
    l_b[_ai] = _arr2[_ai];
    r_b[_ai] = _arr2[_ai];
    l_c[_ai] = _arr3[_ai];
    r_c[_ai] = _arr3[_ai];
    _ai = _ai + 1;
  }
}

void left(int a[N], int b[N], int c[N]) {
  int i = 0;
  while (i < N ) {
    a[i] = a[i] + 1;
    b[i] = b[i] + a[i];
    c[i] = c[i] + b[i];
    i = i + 1;
  }
}