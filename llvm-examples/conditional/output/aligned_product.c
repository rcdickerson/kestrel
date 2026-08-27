#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_age = arb_int();
  int r_age = arb_int();
  assume(l_age == r_age);
  int l_ret_val = 0;
  char r_age_var0[4];
  char r_ret_val[4];
  (*((unsigned int*)(&r_age_var0))) = r_age;
  (*((unsigned int*)(&r_ret_val))) = 0;
  if ((l_age >= 65) && (((int)r_age) < 65)) {
    l_ret_val = 20;
    if (((int)r_age) <= 12) {
      (*((unsigned int*)(&r_ret_val))) = 50;
    }
  } else {
    if ((l_age >= 65) && (!(((int)r_age) < 65))) {
      l_ret_val = 20;
      (*((unsigned int*)(&r_ret_val))) = 20;
    } else {
      if ((!(l_age >= 65)) && (((int)r_age) < 65)) {
        if ((l_age <= 12) && (((int)r_age) <= 12)) {
          l_ret_val = 50;
          (*((unsigned int*)(&r_ret_val))) = 50;
        } else {
          if ((l_age <= 12) && (!(((int)r_age) <= 12))) {
            l_ret_val = 50;
          } else {
            if ((!(l_age <= 12)) && (((int)r_age) <= 12)) {
              (*((unsigned int*)(&r_ret_val))) = 50;
            } else {
            }
          }
        }
      } else {
        if (l_age <= 12) {
          l_ret_val = 50;
        }
        (*((unsigned int*)(&r_ret_val))) = 20;
      }
    }
  }
  sassert(l_ret_val == ((int)(*((unsigned int*)(&r_ret_val)))));
}