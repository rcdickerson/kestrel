#include "seahorn/seahorn.h"

extern int arb_int();
const int N = 10;
int a_1[N + 1];
int a_2[N + 1];

void main() {
  int _i = 0;
  while (_i < N) {
    assume(a_1[_i] == a_2[_i]);
    _i = (_i + 1);
  }
  int l_max = a_1[0];
  int l_maxi = 0;
  int l_i = 0;
  while (l_i <= N) {
    if (l_max < a_1[l_i]) {
      l_max = a_1[l_i];
      l_maxi = l_i;
    }
    l_i = (l_i + 1);
  }
  int l_t = a_1[N];
  a_1[N] = l_max;
  a_1[l_maxi] = l_t;
  int r_j = 0;
  while (r_j <= N) {
    int r_max;
    int r_maxi;
    if (r_j == 0) {
      r_max = a_2[0];
      r_maxi = 0;
    }
    if (r_max < a_2[r_j]) {
      r_max = a_2[r_j];
      r_maxi = r_j;
    }
    if (r_j == N) {
      int r_t = a_2[N];
      a_2[N] = r_max;
      a_2[r_maxi] = r_t;
    }
    r_j = (r_j + 1);
  }
  int _j = 0;
  while (_j < N) {
    sassert(a_1[_j] == a_2[_j]);
    _j = (_j + 1);
  }
 }
