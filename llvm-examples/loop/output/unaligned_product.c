void main(int l_n, int r_n) {
  int l_sum = 0;
  int l_i = 1;
  while (l_i <= l_n) {
    l_sum = (l_sum + l_i);
    l_i = (l_i + 1);
  }
  char r_n_var0[4];
  char r_i[4];
  char r_sum[4];
  (*((unsigned int*)(&r_n_var0))) = r_n;
  (*((unsigned int*)(&r_sum))) = 0;
  (*((unsigned int*)(&r_i))) = 1;
  while (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_n)) {
    (*((unsigned int*)(&r_sum))) = ((*((unsigned int*)(&r_sum))) + (*((unsigned int*)(&r_i))));
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
}