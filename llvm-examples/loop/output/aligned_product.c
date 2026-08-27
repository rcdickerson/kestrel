#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_n = arb_int();
  int r_n = arb_int();
  assume(l_n == r_n);
  int l_sum = 0;
  int l_i = 1;
  char r_n_var0[4];
  char r_i[4];
  char r_sum[4];
  (*((unsigned int*)(&r_n_var0))) = r_n;
  (*((unsigned int*)(&r_sum))) = 0;
  (*((unsigned int*)(&r_i))) = 1;
  while ((l_i <= l_n) && (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n))) {
    l_sum = (l_sum + l_i);
    l_i = (l_i + 1);
    (*((unsigned int*)(&r_sum))) = ((*((unsigned int*)(&r_sum))) + (*((unsigned int*)(&r_i))));
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
  if (l_i <= l_n) {
    while (l_i <= l_n) {
      assume(!(((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)));
      l_sum = (l_sum + l_i);
      l_i = (l_i + 1);
    }
  }
  if (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)) {
    while (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)) {
      assume(!(l_i <= l_n));
      (*((unsigned int*)(&r_sum))) = ((*((unsigned int*)(&r_sum))) + (*((unsigned int*)(&r_i))));
      (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    }
  }
  sassert(l_sum == ((int)(*((unsigned int*)(&r_sum)))));
}