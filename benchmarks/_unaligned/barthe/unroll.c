#include "seahorn/seahorn.h"
extern int havoc(void);

int main(void) {
  int N = havoc();

  int x_1 = 0;
  int i_1 = 0;
  while (i_1 <= N ) {
    x_1 = x_1 + i_1;
    i_1 = i_1 + 1;
  }

  int x_2 = 0;
  int i_2 = 1;
  while (i_2 <= N ) {
    x_2 = x_2 + i_2;
    i_2 = i_2 + 1;
  }

  sassert(x_1 == x_2);
}
