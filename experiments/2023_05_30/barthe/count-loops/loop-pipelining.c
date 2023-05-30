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
  int _i = 0;
  while (_i < N) {
    assume((a_1[_i] == a_2[_i]) && ((b_1[_i] == b_2[_i]) && (c_1[_i] == c_2[_i])));
  }
  int l_i = 0;
  int r_j = 0;
  a_2[0] = (a_2[0] + 1);
  b_2[0] = (b_2[0] + a_2[0]);
  a_2[1] = (a_2[1] + 1);
  while ((l_i < N) && (r_j < (N - 2))) {
    a_1[l_i] = (a_1[l_i] + 1);
    b_1[l_i] = (b_1[l_i] + a_1[l_i]);
    c_1[l_i] = (c_1[l_i] + b_1[l_i]);
    l_i = (l_i + 1);
    a_2[r_j + 2] = (a_2[r_j + 2] + 1);
    b_2[r_j + 1] = (b_2[r_j + 1] + a_2[r_j + 1]);
    c_2[r_j] = (c_2[r_j] + b_2[r_j]);
    r_j = (r_j + 1);
  }
  while ((l_i < N) && (!(r_j < (N - 2)))) {
    a_1[l_i] = (a_1[l_i] + 1);
    b_1[l_i] = (b_1[l_i] + a_1[l_i]);
    c_1[l_i] = (c_1[l_i] + b_1[l_i]);
    l_i = (l_i + 1);
  }
  while ((!(l_i < N)) && (r_j < (N - 2))) {
    a_2[r_j + 2] = (a_2[r_j + 2] + 1);
    b_2[r_j + 1] = (b_2[r_j + 1] + a_2[r_j + 1]);
    c_2[r_j] = (c_2[r_j] + b_2[r_j]);
    r_j = (r_j + 1);
  }
  c_2[r_j] = (c_2[r_j] + b_2[r_j]);
  b_2[r_j + 1] = (b_2[r_j + 1] + a_2[r_j + 1]);
  c_2[r_j + 1] = (c_2[r_j + 1] + b_2[r_j + 1]);
  int _j = 0;
  while (_j < N) {
    sassert((a_1[_j] == a_2[_j]) && ((b_1[_j] == b_2[_j]) && (c_1[_j] == c_2[_j])));
  }
 }
