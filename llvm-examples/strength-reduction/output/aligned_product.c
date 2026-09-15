#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_B = arb_int();
  int l_C = arb_int();
  int l_N = arb_int();
  int l_x = arb_int();
  int r_B = arb_int();
  int r_C = arb_int();
  int r_N = arb_int();
  int r_arg3 = arb_int();
  assume((l_B == r_B) && ((l_C == r_C) && ((l_N == r_N) && ((l_x == r_arg3) && ((l_N == 1) && ((l_B == 1) && (l_C == 1)))))));
  int l_i = 0;
  int l_j = 0;
  char r_N_var0[4];
  char r_C_var1[4];
  char r_B_var2[4];
  char r_j[4];
  char r_i[4];
  char r_x[4];
  (*((unsigned int*)(&r_x))) = r_arg3;
  (*((unsigned int*)(&r_B_var2))) = r_B;
  (*((unsigned int*)(&r_C_var1))) = r_C;
  (*((unsigned int*)(&r_N_var0))) = r_N;
  (*((unsigned int*)(&r_i))) = 0;
  (*((unsigned int*)(&r_j))) = r_C;
  while ((l_i < l_N) && (((int)(*((unsigned int*)(&r_i)))) < ((int)r_N))) {
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
    (*((unsigned int*)(&r_x))) = ((*((unsigned int*)(&r_x))) + (*((unsigned int*)(&r_j))));
    (*((unsigned int*)(&r_j))) = ((*((unsigned int*)(&r_j))) + r_B);
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
  if (l_i < l_N) {
    while (l_i < l_N) {
      assume(!(((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)));
      l_j = ((l_i * l_B) + l_C);
      l_x = (l_x + l_j);
      l_i = (l_i + 1);
    }
  }
  if (((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) {
    while (((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) {
      assume(!(l_i < l_N));
      (*((unsigned int*)(&r_x))) = ((*((unsigned int*)(&r_x))) + (*((unsigned int*)(&r_j))));
      (*((unsigned int*)(&r_j))) = ((*((unsigned int*)(&r_j))) + r_B);
      (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    }
  }
  sassert(l_x == ((int)(*((unsigned int*)(&r_x)))));
}