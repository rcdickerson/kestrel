#include "seahorn/seahorn.h"

#define N 30
int A_1[N];
int A_2[N];

extern int havoc();
extern int shiftArray(int* A, int idx, int amt);

int main(void) {

  for(int i=0; i < N; i++) assume(A_1[i] == A_2[i]);

  int val_1 = havoc();
  int i = 0;
  while( i < N && A_1[i] < val_1) {
    i = i + 1;
  }
  int len_1 = shiftArray(A_1, i, 1);
  assume(len_1 == N + 1); // spec of shiftArray
  A_1[i] = val_1;
  while (i < len_1) {
    i = i + 1;
  }

  int val_2 = havoc();
  int j = 0;
  while( j < N && A_2[j] < val_2) {
    j = j + 1;
  }
  int len_2 = shiftArray(A_2, j, 1);
  assume(len_2 == N + 1); // spec of shiftArray
  A_2[j] = val_2;
  while (j < len_2) {
    j = j + 1;
  }

  sassert(i == j);
}
