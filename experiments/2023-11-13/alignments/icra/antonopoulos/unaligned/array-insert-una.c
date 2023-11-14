#include "assert.h"
const int A_SIZE = 10;
extern int shiftArray(int* A, int idx, int amt);

void main() {
  int l_A[A_SIZE];
  int l_val = nondet();
  int r_A[A_SIZE];
  int r_val = nondet();
  __VERIFIER_assume((l_val > 0) && (r_val > 0));
  int l_i = 0;
  while ((l_i < A_SIZE) && (l_A[l_i] < l_val)) {
    l_i = (l_i + 1);
  }
  int l_len = A_SIZE + 1;
  l_A[l_i] = l_val;
  while (l_i < l_len) {
    l_i = (l_i + 1);
  }
  int r_j = 0;
  while ((r_j < A_SIZE) && (r_A[r_j] < r_val)) {
    r_j = (r_j + 1);
  }
  int r_len = A_SIZE + 1;
  r_A[r_j] = r_val;
  while (r_j < r_len) {
    r_j = (r_j + 1);
  }
  __VERIFIER_assert(l_i == r_j);
 }
