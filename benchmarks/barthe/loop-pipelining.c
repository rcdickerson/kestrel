/* @KESTREL
 * pre: for _i in (0..10) { left.a[_i] == right.a[_i] && left.b[_i] == right.b[_i] && left.c[_i] == right.c[_i] };
 * left: left;
 * right: right;
 * post: for _j in (0..10) { left.a[_j] == right.a[_j] && left.b[_j] == right.b[_j] && left.c[_j] == right.c[_j] };
 */

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

void right(int a[N], int b[N], int c[N]) {
  int j = 0;
  a[0] = a[0] + 1;
  b[0] = b[0] + a[0];
  a[1] = a[1] + 1;

  while (j < N - 2) {
    a[j+2] = a[j+2] + 1;
    b[j+1] = b[j+1] + a[j+1];
    c[j] = c[j] + b[j];
    j = j + 1;
  }
  c[j] = c[j] + b[j];
  b[j+1] = b[j+1] + a[j+1];
  c[j+1] = c[j+1] + b[j+1];
}
