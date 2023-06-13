#include "seahorn/seahorn.h"

extern int arb_int();
const int A_SIZE = 10;
int A_left[A_SIZE + 1];
int A_right[A_SIZE + 1];
extern int shiftArray(int* A, int idx, int amt);

void main() {
  int l_val = arb_int();
  int r_val = arb_int();
  assume((l_val > 0) && (r_val > 0));
  int l_i = 0;
  int r_j = 0;
  while ((l_i < A_SIZE) && (A_left[l_i] < l_val)) {
    l_i = (l_i + 1);
  }
  while ((r_j < A_SIZE) && (A_right[r_j] < r_val)) {
    r_j = (r_j + 1);
  }
  int l_len = A_SIZE + 1;
  A_left[l_i] = l_val;
  while (l_i < l_len) {
    l_i = (l_i + 1);
  }
  int r_len = A_SIZE + 1;
  A_right[r_j] = r_val;
  while (r_j < r_len) {
    r_j = (r_j + 1);
  }
  sassert(l_i == r_j);
 }
