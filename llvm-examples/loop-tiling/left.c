extern int f(int);
const int M = 10;
const int N = 10;

void left(int a[N*M]) {
  int x = 0;
  while (x < N * M) {
    a[x] = f(x);
    x = x + 1;
  }
}