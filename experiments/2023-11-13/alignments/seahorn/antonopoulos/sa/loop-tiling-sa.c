#include "seahorn/seahorn.h"
extern int arb_int();
extern int f(int);
const int M = 10;
const int N = 10;

void main() {
  int l_a[N * M];
  int r_a[N][M];
  assume(1);
  int l_x = 0;
  int r_i = 0;
  if (l_x < (N * M)) {
    l_a[l_x] = f(l_x);
    l_x = (l_x + 1);
  }
  while ((l_x < (N * M)) && (r_i < N)) {
    int r_j = 0;
    while (r_j < M) {
      r_a[r_i][r_j] = f((r_i * N) + r_j);
      r_j = (r_j + 1);
    }
    l_a[l_x] = f(l_x);
    l_x = (l_x + 1);
    r_i = (r_i + 1);
  }
  while (l_x < (N * M)) {
    assume(!(r_i < N));
    l_a[l_x] = f(l_x);
    l_x = (l_x + 1);
  }
  while (r_i < N) {
    assume(!(l_x < (N * M)));
    int r_j = 0;
    while (r_j < M) {
      r_a[r_i][r_j] = f((r_i * N) + r_j);
      r_j = (r_j + 1);
    }
    r_i = (r_i + 1);
  }
  int i = 0;
  while (i < 10) {
    int j = 0;
    while (j < 10) {
      sassert(l_a[(i * 10) + j] == r_a[i][j]);
      j = (j + 1);
    }
    i = (i + 1);
  }
 }
