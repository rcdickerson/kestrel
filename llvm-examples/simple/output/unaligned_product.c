void main(int l_x, int r_x) {
  int l_ret_val = (l_x + 1);
  char r_ret_val[4];
  char r_x_var1[4];
  (*((unsigned int*)(&r_x_var1))) = r_x;
  (*((unsigned int*)(&r_ret_val))) = (r_x + 1);
}