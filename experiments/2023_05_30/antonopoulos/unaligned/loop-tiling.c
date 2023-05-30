#include "seahorn/seahorn.h"

extern int arb_int();
const int M = 10;
const int N = 10;
int a_1[N * M];
int a_2[N][M];
int f[N * M];

void main() {
  assume(1);
  int l_x = 0;
  while (l_x < (N * M)) {
    a_1[l_x] = f[l_x];
    l_x = (l_x + 1);
  }
  int r_i = 0;
  while (r_i < N) {
    int r_j = 0;
    while (r_j < M) {
      a_2[r_i][r_j] = f[(r_i * M) + r_j];
      r_j = (r_j + 1);
    }
    r_i = (r_i + 1);
  }
  int i = 0;
  while (i < N) {
    int j = 0;
    while (j < M) {
      sassert(a_1[i * (M + j)] == a_2[i][j]);
    }
  }
 }
