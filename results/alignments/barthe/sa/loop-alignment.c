#include "seahorn/seahorn.h"

extern int arb_int();
const int N = 20;
int a_1[N + 1];
int b_1[N + 1];
int d_1[N + 1];
int a_2[N + 1];
int b_2[N + 1];
int d_2[N + 1];

void main() {
  int _i = 0;
  while (_i < N) {
    assume((a_1[_i] == a_2[_i]) && (b_1[0] == b_2[0]));
    _i = (_i + 1);
  }
  int r_j = 1;
  d_2[1] = b_2[0];
  while (r_j <= (N - 1)) {
    b_2[r_j] = a_2[r_j];
    d_2[r_j + 1] = b_2[r_j];
    r_j = (r_j + 1);
  }
  b_2[N] = a_2[N];
  int l_i = 1;
  while (l_i <= N) {
    b_1[l_i] = a_1[l_i];
    d_1[l_i] = b_1[l_i - 1];
    l_i = (l_i + 1);
  }
  int _j = 1;
  while (_j < N) {
    sassert(d_1[_j] == d_2[_j]);
    _j = (_j + 1);
  }
 }
