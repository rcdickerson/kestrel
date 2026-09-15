#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  assume((l_x == r_x) && ((l_x > -2) && (l_x < 2)));
  int l_y = 0;
  int l_z = (2 * l_x);
  int l_i = 0;
  char r_z[4];
  char r_i[4];
  char r_y[4];
  (*((unsigned int*)(&r_z))) = r_x;
  (*((unsigned int*)(&r_y))) = 0;
  (*((unsigned int*)(&r_i))) = 0;
  while ((l_i < l_z) && (((int)(*((unsigned int*)(&r_i)))) < ((int)r_x))) {
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
    (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + r_x);
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
  if (l_i < l_z) {
    while (l_i < l_z) {
      assume(!(((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)));
      l_y = (l_y + l_x);
      l_i = (l_i + 1);
    }
  }
  if (((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) {
    while (((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) {
      assume(!(l_i < l_z));
      (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + r_x);
      (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    }
  }
  (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) * 2);
  sassert(l_y == ((int)(*((unsigned int*)(&r_y)))));
}