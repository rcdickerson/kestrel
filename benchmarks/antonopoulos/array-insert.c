/* @KESTREL
 * pre 1.A == 2.A
    && 1.A_len == length(1.A)
    && 2.A_len == length(2.A);
 * left left;
 * right right;
 * post 1.i == 2.j;
 */

extern int shiftArray(int* A, int idx, int amt);

int left(int A[], int A_len, int val) {
  int i = 0;
  while( i < A_len && A[i] < val) {
    i = i + 1;
  }
  int len = shiftArray(A, i, 1);
  assume(len == A_len + 1); // spec of shiftArray
  A[i] = val;
  while (i < len) {
    i = i + 1;
  }
  return i;
}

int right(int A[], int A_len, int val) {
  int j = 0;
  while( j < A_len && A[j] < val) {
    j = j + 1;
  }
  int len = shiftArray(A, j, 1);
  assume(len == A_len+ 1); // spec of shiftArray
  A[j] = val;
  while (j < len) {
    j = j + 1;
  }
  return j;
}
