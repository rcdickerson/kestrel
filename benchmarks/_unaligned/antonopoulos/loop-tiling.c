extern int f(int);

#define M 10
#define N 10

int a_1[N*M];
int a_2[N][M];

int main(void) {

  int x = 0;
  while (x < N * M) {
    a_1[x] = f(x);
    x = x + 1;
  }

  int i = 0;
  while (i < N) {
    int j = 0;
    while (j < M) {
      a_2[i][j] = f(i*M+j);
      j = j + 1;
    }
    i = i + 1;
  }

  for(int i = 0; i < N; i++) {
    for(int j = 0; j < M; j++) {
      sassert(a_1[i * M + j] == a_2[i][j]);
    }
  }
}
