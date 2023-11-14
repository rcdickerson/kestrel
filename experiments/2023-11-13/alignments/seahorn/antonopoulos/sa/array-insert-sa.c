#include "seahorn/seahorn.h"
extern int arb_int();
const int A_SIZE = 10;
extern int shiftArray(int* A, int idx, int amt);

void main() {
  int l_A[A_SIZE];
  int l_val = arb_int();
  int r_A[A_SIZE];
  int r_val = arb_int();
  assume((l_val > 0) && (r_val > 0));
  int l_i = 0;
  int r_j = 0;
  if ((r_j < A_SIZE) && (r_A[r_j] < r_val)) {
    r_j = (r_j + 1);
  }
  if ((r_j < A_SIZE) && (r_A[r_j] < r_val)) {
    r_j = (r_j + 1);
  }
  while (((l_i < A_SIZE) && (l_A[l_i] < l_val)) && ((r_j < A_SIZE) && (r_A[r_j] < r_val))) {
    r_j = (r_j + 1);
    l_i = (l_i + 1);
  }
  while ((l_i < A_SIZE) && (l_A[l_i] < l_val)) {
    assume(!((r_j < A_SIZE) && (r_A[r_j] < r_val)));
    l_i = (l_i + 1);
  }
  while ((r_j < A_SIZE) && (r_A[r_j] < r_val)) {
    assume(!((l_i < A_SIZE) && (l_A[l_i] < l_val)));
    r_j = (r_j + 1);
  }
  int l_len = A_SIZE + 1;
  l_A[l_i] = l_val;
  int r_len = A_SIZE + 1;
  r_A[r_j] = r_val;
  if (r_j < r_len) {
    r_j = (r_j + 1);
  }
  if (r_j < r_len) {
    r_j = (r_j + 1);
  }
  while ((l_i < l_len) && (r_j < r_len)) {
    r_j = (r_j + 1);
    l_i = (l_i + 1);
  }
  while (l_i < l_len) {
    assume(!(r_j < r_len));
    l_i = (l_i + 1);
  }
  while (r_j < r_len) {
    assume(!(l_i < l_len));
    r_j = (r_j + 1);
  }
  sassert(l_i == r_j);
 }
