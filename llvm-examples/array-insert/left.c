const int A_SIZE = 10;

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