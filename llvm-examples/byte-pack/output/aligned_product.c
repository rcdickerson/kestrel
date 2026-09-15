#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_n = arb_int();
  int r_n = arb_int();
  assume(l_n == r_n);
  int l_prod = l_n;
  char r_prod[4];
  (*((unsigned int*)(&r_prod))) = r_n;
  sassert(l_prod == ((int)(*((unsigned int*)(&r_prod)))));
}