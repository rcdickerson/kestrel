/* @KESTREL
 * pre: left.k == right.k && left.x == right.x &&
        for _i in (0..10) { left.a[_i] == right.a[_i] && left.b[_i] == right.b[_i] && left.c[_i] == right.c[_i]};
 * left: left;
 * right: right;
 * post: for _j in (0..10) { left.a[_j] == right.a[_j] && left.b[_j] == right.b[_j] && left.c[_j] == right.c[_j] };
 */

#define N 10

void _test_gen(int _arr1[N], int _arr2[N], int _arr3[N], int _k, int _x) {
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
  int l_k = _k;
  int r_k = _k;
  int l_x = _x;
  int r_x = _x;
}

void left(int a[N], int b[N], int c[N], int k, int x) {
  int i = 0;
  while (i < N) {
    a[i] = a[i] + k;
    if (x < 7) {
      b[i] = a[i] * c[i];
    } else {
      b[i] = a[i - 1] * b[i - 1];
    }
    i = i + 1;
  }
}

void right(int a[N], int b[N], int c[N], int k, int x) {
  if (x < 7) {
    int j = 0;
    while (j < N) {
      a[j] = a[j] + k;
      b[j] = a[j] * c[j];
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < N) {
      a[j] = a[j] + k;
      b[j] = a[j - 1] * b[j - 1];
      j = j + 1;
    }
  }
}
