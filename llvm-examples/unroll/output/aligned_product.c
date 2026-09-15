#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_N = arb_int();
  int r_N = arb_int();
  assume(l_N == r_N);
  int l_x = 0;
  int l_i = 0;
  char r_N_var0[4];
  char r_i[4];
  char r_x[4];
  (*((unsigned int*)(&r_N_var0))) = r_N;
  (*((unsigned int*)(&r_x))) = 0;
  (*((unsigned int*)(&r_i))) = 1;
  while ((l_i <= l_N) && (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N))) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
    (*((unsigned int*)(&r_x))) = ((*((unsigned int*)(&r_x))) + (*((unsigned int*)(&r_i))));
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
  if (l_i <= l_N) {
    while (l_i <= l_N) {
      assume(!(((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)));
      l_x = (l_x + l_i);
      l_i = (l_i + 1);
    }
  }
  if (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) {
    while (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) {
      assume(!(l_i <= l_N));
      (*((unsigned int*)(&r_x))) = ((*((unsigned int*)(&r_x))) + (*((unsigned int*)(&r_i))));
      (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    }
  }
  sassert(l_x == ((int)(*((unsigned int*)(&r_x)))));
}