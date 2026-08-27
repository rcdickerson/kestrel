#include "seahorn/seahorn.h"
extern int arb_int();
void main() {
  int l_a = arb_int();
  int l_b = arb_int();
  int l_c = arb_int();
  int r_a = arb_int();
  int r_b = arb_int();
  int r_c = arb_int();
  assume((l_a == r_a) && ((l_b == r_b) && (l_c == r_c)));
  int l_sum = (l_a + l_b);
  int l_prod = (l_sum * l_c);
  char r_prod[4];
  char r_sum[4];
  char r_c_var2[4];
  char r_b_var3[4];
  char r_a_var4[4];
  int r_val5;
  (*((unsigned int*)(&r_a_var4))) = r_a;
  (*((unsigned int*)(&r_b_var3))) = r_b;
  (*((unsigned int*)(&r_c_var2))) = r_c;
  r_val5 = (r_a + r_b);
  (*((unsigned int*)(&r_sum))) = r_val5;
  (*((unsigned int*)(&r_prod))) = (r_val5 * r_c);
  sassert(l_prod == (*((unsigned int*)(&r_prod))));
}