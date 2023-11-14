#include "assert.h"
const float epsilon = 0.01;

void main() {
  float l_a[10];
  float r_a[10];
  int _i = 1;
  while (_i < 10) {
    __VERIFIER_assume(((l_a[_i] >= r_a[_i]) || ((r_a[_i] - l_a[_i]) < epsilon)) && ((l_a[_i] < r_a[_i]) || ((l_a[_i] - r_a[_i]) < epsilon)));
    _i = (_i + 1);
  }
  int l_i = 0;
  int r_i = 0;
  while ((l_i < 10) && (r_i < 10)) {
    int l_j = 10 - 1;
    int r_j = 10 - 1;
    while ((l_j > l_i) && (r_j > r_i)) {
      if (l_a[l_j - 1] > l_a[l_j]) {
        float l_temp = l_a[l_j];
        l_a[l_j] = l_a[l_j - 1];
        l_a[l_j - 1] = l_temp;
      }
      if (r_a[r_j - 1] > r_a[r_j]) {
        float r_temp = r_a[r_j];
        r_a[r_j] = r_a[r_j - 1];
        r_a[r_j - 1] = r_temp;
      }
      l_j = (l_j - 1);
      r_j = (r_j - 1);
    }
    while (l_j > l_i) {
      __VERIFIER_assume(!(r_j > r_i));
      if (l_a[l_j - 1] > l_a[l_j]) {
        float l_temp = l_a[l_j];
        l_a[l_j] = l_a[l_j - 1];
        l_a[l_j - 1] = l_temp;
      }
      l_j = (l_j - 1);
    }
    while (r_j > r_i) {
      __VERIFIER_assume(!(l_j > l_i));
      if (r_a[r_j - 1] > r_a[r_j]) {
        float r_temp = r_a[r_j];
        r_a[r_j] = r_a[r_j - 1];
        r_a[r_j - 1] = r_temp;
      }
      r_j = (r_j - 1);
    }
    l_i = (l_i + 1);
    r_i = (r_i + 1);
  }
  while (l_i < 10) {
    __VERIFIER_assume(!(r_i < 10));
    int l_j = 10 - 1;
    while (l_j > l_i) {
      if (l_a[l_j - 1] > l_a[l_j]) {
        float l_temp = l_a[l_j];
        l_a[l_j] = l_a[l_j - 1];
        l_a[l_j - 1] = l_temp;
      }
      l_j = (l_j - 1);
    }
    l_i = (l_i + 1);
  }
  while (r_i < 10) {
    __VERIFIER_assume(!(l_i < 10));
    int r_j = 10 - 1;
    while (r_j > r_i) {
      if (r_a[r_j - 1] > r_a[r_j]) {
        float r_temp = r_a[r_j];
        r_a[r_j] = r_a[r_j - 1];
        r_a[r_j - 1] = r_temp;
      }
      r_j = (r_j - 1);
    }
    r_i = (r_i + 1);
  }
  int _j = 1;
  while (_j < 10) {
    __VERIFIER_assert(((l_a[_j] >= r_a[_j]) || ((r_a[_j] - l_a[_j]) < epsilon)) && ((l_a[_j] < r_a[_j]) || ((l_a[_j] - r_a[_j]) < epsilon)));
    _j = (_j + 1);
  }
 }
