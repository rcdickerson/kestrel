extern int arb_int(void);
extern int f(int);

int main(void) {
  int N = arb_int();
  int M = arb_int();

  rel_left();

  int x = 0;
  while (x < N * M) {
    a[x] := f(x);
    x = x + 1;
  }

  rel_mid();

  int i = 0;
  while (i < N) {
    int j = 0;
    while (j < M) {
      A[i][j] := f(i*M+j);
      j = j + 1;
    }
    i = i + 1;
  }

  rel_right();

  sassert(x1 == x2);
}
