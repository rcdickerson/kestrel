#include "seahorn/seahorn.h"

extern int arb_int();
const int M = 5;
const int N = 10;
const int L = 10;
int a[N][L];
int b[N];
int s_1[(N - M) + 1];
int s_2[(N - M) + 1];

void main() {
  assume(1);
  int l_i = 0;
  s_2[0] = 0;
  int r_k = 0;
  while (r_k <= (M - 1)) {
    b[r_k] = 0;
    int r_l = 0;
    while (r_l <= (L - 1)) {
      b[r_k] = (b[r_k] + a[r_k][r_l]);
      r_l = (r_l + 1);
    }
    s_2[0] = (s_2[0] + b[r_k]);
    r_k = (r_k + 1);
  }
  int r_i = 1;
  while ((l_i < (N - M)) && (r_i <= (N - M))) {
    s_1[l_i] = 0;
    int l_k = 0;
    while (l_k <= (M - 1)) {
      int l_l = 0;
      while (l_l <= (L - 1)) {
        s_1[l_i] = (s_1[l_i] + a[l_i + l_k][l_l]);
        l_l = (l_l + 1);
      }
    }
    b[(r_i + M) - 1] = 0;
    int r_l = 0;
    while (r_l <= (L - 1)) {
      b[(r_i + M) - 1] = (b[(r_i + M) - 1] + a[(r_i + M) - 1][r_l]);
      r_l = (r_l + 1);
    }
    int r_z = b[(r_i + M) - 1] - b[r_i - 1];
    s_2[r_i] = (s_2[r_i - 1] + r_z);
    r_i = (r_i + 1);
  }
  while ((l_i < (N - M)) && (!(r_i <= (N - M)))) {
    s_1[l_i] = 0;
    int l_k = 0;
    while (l_k <= (M - 1)) {
      int l_l = 0;
      while (l_l <= (L - 1)) {
        s_1[l_i] = (s_1[l_i] + a[l_i + l_k][l_l]);
        l_l = (l_l + 1);
      }
    }
  }
  while ((!(l_i < (N - M))) && (r_i <= (N - M))) {
    b[(r_i + M) - 1] = 0;
    int r_l = 0;
    while (r_l <= (L - 1)) {
      b[(r_i + M) - 1] = (b[(r_i + M) - 1] + a[(r_i + M) - 1][r_l]);
      r_l = (r_l + 1);
    }
    int r_z = b[(r_i + M) - 1] - b[r_i - 1];
    s_2[r_i] = (s_2[r_i - 1] + r_z);
    r_i = (r_i + 1);
  }
  int i = 0;
  while (i < (N - (M + 1))) {
    sassert(s_1[i] == s_2[i]);
  }
 }
