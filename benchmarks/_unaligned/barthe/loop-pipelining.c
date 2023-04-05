#include "seahorn/seahorn.h"

#define N 10
int a[N];
int b[N];
int c[N];
int a_2[N];
int b_2[N];
int c_2[N];

int main(void) {

  for (int i = 0; i < N; i++) assume(a[i] == a_2[i]);
  for (int i = 0; i < N; i++) assume(b[i] == b_2[i]);
  for (int i = 0; i < N; i++) assume(c[i] == c_2[i]);

  int i = 0;
  while (i < N ) {
    a[i] = a[i] + 1;
    b[i] = b[i] + a[i];
    c[i] = c[i] + b[i];
    i = i + 1;
  }

  int j = 0;
  a_2[0] = a_2[0] + 1;
  b_2[0] = b_2[0] + a_2[0];
  a_2[1] = a_2[1] + 1;

  while (j < N - 2) {
    a_2[j+2] = a_2[j+2] + 1;
    b_2[j+1] = b_2[j+1] + a_2[j+1];
    c_2[j] = c_2[j] + b_2[j];
    j = j + 1;
  }
  c_2[j] = c_2[j] + b_2[j];
  b_2[j+1] = b_2[j+1] + a_2[j+1];
  c_2[j+1] = c_2[j+1] + b_2[j+1];

  for (int i = 0; i < N; i++) sassert(a[i] == a_2[i]);
  for (int i = 0; i < N; i++) sassert(b[i] == b_2[i]);
  for (int i = 0; i < N; i++) sassert(c[i] == c_2[i]);

  return 0;
}
