/* @KESTREL
 * pre:   true;
 * left:  left;
 * right: right;
 * post:  for i in (0..1000) {
            for j in (0..1000) {
              left.a[i * 1000 + j] == right.a[i][j]
            }
          };
 */

extern int f(int);
const int M = 1000;
const int N = 1000;

void left(int a[N*M]) {
  int x = 0;
  while (x < N * M) {
    a[x] = f(x);
    x = x + 1;
  }
}

void right(int a[N][M]) {
  int i = 0;
  while (i < N) {
    int j = 0;
    while (j < M) {
      a[i][j] = f(i*M+j);
      j = j + 1;
    }
    i = i + 1;
  }
}
