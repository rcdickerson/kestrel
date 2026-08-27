#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_a = arb_int();
  int l_b = arb_int();
  int r_arg0 = arb_int();
  int r_b = arb_int();
  assume((l_a == r_arg0) && (l_b == r_b));
  int l_c = 0;
  char r_b_var0[4];
  char r_c[4];
  char r_a[4];
  (*((unsigned int*)(&r_a))) = r_arg0;
  (*((unsigned int*)(&r_b_var0))) = r_b;
  (*((unsigned int*)(&r_c))) = 0;
  while ((l_a < l_b) && (((int)(*((unsigned int*)(&r_a)))) < ((int)r_b))) {
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
    (*((unsigned int*)(&r_c))) = ((*((unsigned int*)(&r_c))) + ((*((unsigned int*)(&r_a))) * (*((unsigned int*)(&r_a)))));
    (*((unsigned int*)(&r_a))) = ((*((unsigned int*)(&r_a))) + 1);
  }
  if (l_a < l_b) {
    while (l_a < l_b) {
      assume(!(((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)));
      l_c = (l_c + (l_a * l_a));
      l_a = (l_a + 1);
    }
  }
  if (((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) {
    while (((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) {
      assume(!(l_a < l_b));
      (*((unsigned int*)(&r_c))) = ((*((unsigned int*)(&r_c))) + ((*((unsigned int*)(&r_a))) * (*((unsigned int*)(&r_a)))));
      (*((unsigned int*)(&r_a))) = ((*((unsigned int*)(&r_a))) + 1);
    }
  }
  sassert(l_c == ((int)(*((unsigned int*)(&r_c)))));
}