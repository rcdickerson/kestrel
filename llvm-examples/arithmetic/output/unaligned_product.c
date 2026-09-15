void main(int l_a, int l_b, int l_c, int r_a, int r_b, int r_c) {
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
}