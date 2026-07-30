#define N 10

void _test_gen(int _arr[N+1]) {
  int _ai = 0;
  int l_a[N+1];
  int r_a[N+1];
  while (_ai < N) {
    l_a[_ai] = _arr[_ai];
    r_a[_ai] = _arr[_ai];
    _ai = _ai + 1;
  }
}

void left(int a[N+1]) {
  int max = a[0];
  int maxi = 0;
  int i = 0;
  while (i < N) {
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