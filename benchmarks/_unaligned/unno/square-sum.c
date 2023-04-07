#include "seahorn/seahorn.h"

extern int arb_int();

int main(void) {

  int a = arb_int();
  int b = arb_int();

  int a1 = a;
  int b1 = b;
  int c1 = 0;
  while (a1 < b1) {
   c1 = c1 + (a1 * a1);
   a1 = a1 + 1;
  }

  int a2 = a;
  int b2 = b;
  int c2 = 0;
  while (a2 < b2) {
   c2 = c2 + (a2 * a2);
   a2 = a2 + 1;
  }

  sassert(c1 == c2);
}
