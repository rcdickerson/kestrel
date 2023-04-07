/* #include "seahorn/seahorn.h" */

// extern int havoc(void);

/* #define N 10 */
/* int a_1[N]; */
/* int b_1[N]; */
/* int c_1[N]; */
/* int a_2[N]; */
/* int b_2[N]; */
/* int c_2[N]; */

int main(void) {

//  for (int i = 0; i < N; i++) assume(a_1[i] == a_2[i]);
//  for (int i = 0; i < N; i++) assume(b_1[i] == b_2[i]);
//  for (int i = 0; i < N; i++) assume(c_1[i] == c_2[i]);

  rel_left();

  int k = havoc();
  int x = havoc();

  int i = 0;
  while (i < N) {
    a_1[i] = a_1[i] + k;
    if (x < 7) {
      b_1[i] = a_1[i] * c_1[i];
    } else {
      b_1[i] = a_1[i - 1] * b_1[i - 1];
    }
    i = i + 1;
  }

  rel_mid();

  if (x < 7) {
    int j = 0;
    while (j < N) {
      a_2[j] = a_2[j] + k;
      b_2[j] = a_2[j] * c_2[j];
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < N) {
      a_2[j] = a_2[j] + k;
      b_2[j] = a_2[j - 1] * b_2[j - 1];
      j = j + 1;
    }
  }

  rel_right();

//  for (int i = 0; i < N; i++) sassert(a_1[i] == a_2[i]);
//  for (int i = 0; i < N; i++) sassert(b_1[i] == b_2[i]);
//  for (int i = 0; i < N; i++) sassert(c_1[i] == c_2[i]);
}
