//#include "seahorn/seahorn.h"

//#define M 5
//#define N 10
//#define L 10
//int a[N][L];
//int b[N];
//int s_1[N-M+1];
//int s_2[N-M+1];

int main(void) {

  rel_left();

  int i_1 = 0;
  while (i_1 < N - M) {
    s_1[i_1] = 0;
    int k_1 = 0;
    while (k_1 <= M - 1) {
      int l = 0;
      while (l <= L - 1) {
        s_1[i_1] = s_1[i_1] + a[i_1 + k_1][l];
        l = l + 1;
      }
    }
  }

  rel_mid();

  s_2[0] = 0;
  int k_2 = 0;
  while (k_2 <= M - 1) {
    b[k_2] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[k_2] = b[k_2] + a[k_2][l];
      l = l + 1;
    }
    s_2[0] = s_2[0] + b[k_2];
    k_2 = k_2 + 1;
  }
  int i_2 = 1;
  while(i_2 <= N - M) {
    b[i_2 + M - 1] = 0;
    int l = 0;
    while (l <= L - 1) {
      b[i_2+M-1] = b[i_2 + M - 1] + a[i_2 + M - 1][l];
      l = l + 1;
    }
    int z = b[i_2 + M - 1] - b[i_2 - 1];
    s_2[i_2] = s_2[i_2 - 1] + z;
    i_2 = i_2 + 1;
  }

  rel_right();

//  for (int i = 0; i < N - M + 1; i++) sassert(s_1[i] == s_2[i]);
}
