/* @KESTREL
 * pre: true;
 * left: left;
 * right: right;
 * post: for i in (0..(N - M + 1)) { s_1[i] == s_2[i] };
 */

const int M = 5;
const int N = 10;
const int L = 10;

int a[N][L];
int b[N];
int s_1[N-M+1];
int s_2[N-M+1];

void left(void) {
  int i = 0;
  while (i < N - M) {
    s_1[i] = 0;
    int k = 0;
    while (k <= M - 1) {
      int l = 0;
      while (l <= L - 1) {
        s_1[i] = s_1[i] + a[i + k][l];
        l = l + 1;
      }
    }
  }
}

void right(void) {
  s_2[0] = 0;
  int k = 0;
  while (k <= M - 1) {
    b[k] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[k] = b[k] + a[k][l];
      l = l + 1;
    }
    s_2[0] = s_2[0] + b[k];
    k = k + 1;
  }
  int i = 1;
  while(i <= N - M) {
    b[i + M - 1] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[i+M-1] = b[i + M - 1] + a[i + M - 1][l];
      l = l + 1;
    }
    int z = b[i + M - 1] - b[i - 1];
    s_2[i] = s_2[i - 1] + z;
    i = i + 1;
  }
}
