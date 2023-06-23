/* @KESTREL
 * pre: for _i in (0..N) { left.a[_i] == right.a[_i] };
 * left: left;
 * right: right;
 * post: for _j in (0..N) { left.a[_j] == right.a[_j] };
 */

#define N 10

void _generator(int _arr[N + 1]) {
  int _ai = 0;
  int l_a[N + 1];
  int r_a[N + 1];
  while (_ai <= N) {
    l_a[_ai] = _arr[_ai];
    r_a[_ai] = _arr[_ai];
    _ai = _ai + 1;
  }
}

void left(int a[N + 1]) {
  int max = a[0];
  int maxi = 0;
  int i = 0;
  while (i <= N) {
    if (max < a[i]) {
      max = a[i];
      maxi = i;
    }
    i = i + 1;
  }
  int t = a[N];
  a[N] = max;
  a[maxi] = t;
}

void right(int a[N + 1]) {
  int j = 0;
  while (j <= N) {
    int max;
    int maxi;
    if (j == 0) {
      max = a[0];
      maxi = 0;
    }
    if (max < a[j]) {
      max = a[j];
      maxi = j;
    }
    if (j == N) {
      int t = a[N];
      a[N] = max;
      a[maxi] = t;
    }
    j = j + 1;
  }
}
