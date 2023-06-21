/* @KESTREL
 * pre: left.val > 0 && right.val > 0;
 * left: left;
 * right: right;
 * post: left.i == right.j;
 */

const int A_SIZE = 100;

extern int shiftArray(int* A, int idx, int amt);

void left(int A[A_SIZE], int val) {
  int i = 0;
  while( i < A_SIZE && A[i] < val) {
    i = i + 1;
  }
  // int len = shiftArray(A_left, i, 1);
  int len = A_SIZE + 1; // spec of shiftArray
  A[i] = val;
  while (i < len) {
    i = i + 1;
  }
}

void right(int A[A_SIZE], int val) {
  int j = 0;
  while( j < A_SIZE && A[j] < val) {
    j = j + 1;
  }
  // int len = shiftArray(A_left, i, 1);
  int len = A_SIZE + 1; // spec of shiftArray
  A[j] = val;
  while (j < len) {
    j = j + 1;
  }
}
