#include "seahorn/seahorn.h"

extern int arb_int();
const int N = 10;
float a_1[N];
float a_2[N];
const float epsilon = 0.01;

void main() {
  int _i = 1;
  while (_i < N) {
    assume(((a_1[_i] >= a_2[_i]) || ((a_2[_i] - a_1[_i]) < epsilon)) && ((a_1[_i] < a_2[_i]) || ((a_1[_i] - a_2[_i]) < epsilon)));
    _i = (_i + 1);
  }
  int l_i = 0;
  int r_i = 0;
  while ((l_i < N) && (r_i < N)) {
    int l_j = N - 1;
    int r_j = N - 1;
    while (r_j > r_i) {
      if (a_2[r_j - 1] > a_2[r_j]) {
        float r_temp = a_2[r_j];
        a_2[r_j] = a_2[r_j - 1];
        a_2[r_j - 1] = r_temp;
      }
      r_j = (r_j - 1);
    }
    while (l_j > l_i) {
      if (a_1[l_j - 1] > a_1[l_j]) {
        float l_temp = a_1[l_j];
        a_1[l_j] = a_1[l_j - 1];
        a_1[l_j - 1] = l_temp;
      }
      l_j = (l_j - 1);
    }
    r_i = (r_i + 1);
    l_i = (l_i + 1);
  }
  while ((l_i < N) && (!(r_i < N))) {
    int l_j = N - 1;
    while (l_j > l_i) {
      if (a_1[l_j - 1] > a_1[l_j]) {
        float l_temp = a_1[l_j];
        a_1[l_j] = a_1[l_j - 1];
        a_1[l_j - 1] = l_temp;
      }
      l_j = (l_j - 1);
    }
    l_i = (l_i + 1);
  }
  while ((!(l_i < N)) && (r_i < N)) {
    int r_j = N - 1;
    while (r_j > r_i) {
      if (a_2[r_j - 1] > a_2[r_j]) {
        float r_temp = a_2[r_j];
        a_2[r_j] = a_2[r_j - 1];
        a_2[r_j - 1] = r_temp;
      }
      r_j = (r_j - 1);
    }
    r_i = (r_i + 1);
  }
  int _j = 1;
  while (_j < N) {
    sassert(((a_1[_j] >= a_2[_j]) || ((a_2[_j] - a_1[_j]) < epsilon)) && ((a_1[_j] < a_2[_j]) || ((a_1[_j] - a_2[_j]) < epsilon)));
    _j = (_j + 1);
  }
 }
