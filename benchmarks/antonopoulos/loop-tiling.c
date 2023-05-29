/* @KESTREL
 * pre:   true;
 * left:  left;
 * right: right;
 * post:  for i in (0..N) {
            for j in (0..M) {
              a_1[i * M + j] == a_2[i][j]
            }
          };
 */

extern int f(int);

const int M = 10;
const int N = 10;

int a_1[N*M];
int a_2[N][M];

void left(void) {
  int x = 0;
  while (x < N * M) {
    a_1[x] = f(x);
    x = x + 1;
  }
}

void right(void) {
  int i = 0;
  while (i < N) {
    int j = 0;
    while (j < M) {
      a_2[i][j] = f(i*M+j);
      j = j + 1;
    }
    i = i + 1;
  }
}
