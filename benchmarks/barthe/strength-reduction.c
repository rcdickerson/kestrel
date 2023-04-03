//#include "seahorn/seahorn.h"
//extern int arb_int(void);

int main(void) {
  int B = arb_int();
  int C = arb_int();
  int N = arb_int();

  int x = arb_int();

  rel_left();

  int x_1 = x;
  int i_1 = 0;
  int j_1 = 0;
  while (i_1 < N ) {
    j_1 = i_1 * B + C;
    x_1 = x_1 + j_1;
    i_1 = i_1 + 1;
  }

  rel_mid();

  int x_2 = x;
  int i_2 = 0;
  int j_2 = C;
  while (i_2 < N ) {
    x_2 = x_2 + j_2;
    j_2 = j_2 + B;
    i_2 = i_2 + 1;
  }

  rel_right();

//  sassert(x_1 == x_2);
}
