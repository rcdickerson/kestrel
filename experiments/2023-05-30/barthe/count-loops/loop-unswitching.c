#include "seahorn/seahorn.h"

extern int arb_int();
const int N = 10;
int a_1[N];
int b_1[N];
int c_1[N];
int a_2[N];
int b_2[N];
int c_2[N];

void main() {
  int l_k = arb_int();
  int l_x = arb_int();
  int r_k = arb_int();
  int r_x = arb_int();
  assume((l_k == r_k) && (l_x == r_x));
  int _i = 0;
  while (_i < N) {
    assume((a_1[_i] == a_2[_i]) && ((b_1[_i] == b_2[_i]) && (c_1[_i] == c_2[_i])));
  }
  int l_i = 0;
  while (l_i < N) {
    a_1[l_i] = (a_1[l_i] + l_k);
    if (l_x < 7) {
      b_1[l_i] = (a_1[l_i] * c_1[l_i]);
    } else {b_1[l_i] = (a_1[l_i - 1] * b_1[l_i - 1]);
    }
    l_i = (l_i + 1);
  }
  if (r_x < 7) {
    int r_j = 0;
    while (r_j < N) {
      a_2[r_j] = (a_2[r_j] + r_k);
      b_2[r_j] = (a_2[r_j] * c_2[r_j]);
      r_j = (r_j + 1);
    }
  } else {int r_j = 0;
    while (r_j < N) {
      a_2[r_j] = (a_2[r_j] + r_k);
      b_2[r_j] = (a_2[r_j - 1] * b_2[r_j - 1]);
      r_j = (r_j + 1);
    }
  }
  int _j = 0;
  while (_j < N) {
    sassert((a_1[_j] == a_2[_j]) && ((b_1[_j] == b_2[_j]) && (c_1[_j] == c_2[_j])));
  }
 }
