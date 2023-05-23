/* @KESTREL
 * pre: left.A == right.A;
 * left: left;
 * right: right;
 * post: left.i == right.j;
 */

const int A_SIZE = 10;
int A_left[A_SIZE];
int A_right[A_SIZE];

extern int shiftArray(int* A, int idx, int amt);

void left(int val) {
  int i = 0;
  while( i < A_SIZE && A_left[i] < val) {
    i = i + 1;
  }
  int len = shiftArray(A_left, i, 1);
  assume(len == A_SIZE + 1); // spec of shiftArray
  A_left[i] = val;
  while (i < len) {
    i = i + 1;
  }
}

void right(int val) {
  int j = 0;
  while( j < A_SIZE && A_right[j] < val) {
    j = j + 1;
  }
  int len = shiftArray(A_right, j, 1);
  assume(len == A_SIZE + 1); // spec of shiftArray
  A_right[j] = val;
  while (j < len) {
    j = j + 1;
  }
}
