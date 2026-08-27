#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_low = arb_int();
  int l_h = arb_int();
  int r_low = arb_int();
  int r_h = arb_int();
  assume((l_low == r_low) && ((l_low > l_h) && ((l_h > 0) && ((r_low > r_h) && (r_h > 0)))));
  int l_i = 0;
  int l_y = 0;
  int l_v = 0;
  char r_h_var0[4];
  char r_low_var1[4];
  char r_v[4];
  char r_y[4];
  char r_i[4];
  (*((unsigned int*)(&r_low_var1))) = r_low;
  (*((unsigned int*)(&r_h_var0))) = r_h;
  (*((unsigned int*)(&r_i))) = 0;
  (*((unsigned int*)(&r_y))) = 0;
  (*((unsigned int*)(&r_v))) = 0;
  while ((l_h > l_i) && (((int)r_h) > ((int)(*((unsigned int*)(&r_i)))))) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + (*((unsigned int*)(&r_y))));
  }
  if (l_h > l_i) {
    while (l_h > l_i) {
      assume(!(((int)r_h) > ((int)(*((unsigned int*)(&r_i))))));
      l_i = (l_i + 1);
      l_y = (l_y + l_y);
    }
  }
  if (((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) {
    while (((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) {
      assume(!(l_h > l_i));
      (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
      (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + (*((unsigned int*)(&r_y))));
    }
  }
  l_v = 1;
  (*((unsigned int*)(&r_v))) = 1;
  while ((l_low > l_i) && (((int)r_low) > ((int)(*((unsigned int*)(&r_i)))))) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + (*((unsigned int*)(&r_y))));
  }
  if (l_low > l_i) {
    while (l_low > l_i) {
      assume(!(((int)r_low) > ((int)(*((unsigned int*)(&r_i))))));
      l_i = (l_i + 1);
      l_y = (l_y + l_y);
    }
  }
  if (((int)r_low) > ((int)(*((unsigned int*)(&r_i))))) {
    while (((int)r_low) > ((int)(*((unsigned int*)(&r_i))))) {
      assume(!(l_low > l_i));
      (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
      (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + (*((unsigned int*)(&r_y))));
    }
  }
  sassert(l_y == ((int)(*((unsigned int*)(&r_y)))));
}