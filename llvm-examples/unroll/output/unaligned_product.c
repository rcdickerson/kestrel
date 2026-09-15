void main(int l_N, int r_N) {
  int l_x = 0;
  int l_i = 0;
  while (l_i <= l_N) {
    l_x = (l_x + l_i);
    l_i = (l_i + 1);
  }
  char r_N_var0[4];
  char r_i[4];
  char r_x[4];
  (*((unsigned int*)(&r_N_var0))) = r_N;
  (*((unsigned int*)(&r_x))) = 0;
  (*((unsigned int*)(&r_i))) = 1;
  while (((int)(*((unsigned int*)(&r_i)))) <= ((int)r_N)) {
    (*((unsigned int*)(&r_x))) = ((*((unsigned int*)(&r_x))) + (*((unsigned int*)(&r_i))));
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
}