#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_x = arb_int();
  int r_x = arb_int();
  assume(l_x == r_x);
  int l_ret_val = (l_x + 1);
  char r_ret_val[4];
  char r_x_var1[4];
  (*((unsigned int*)(&r_x_var1))) = r_x;
  (*((unsigned int*)(&r_ret_val))) = (r_x + 1);
  sassert(l_ret_val == ((int)(*((unsigned int*)(&r_ret_val)))));
}