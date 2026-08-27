void main(int l_B, int l_C, int l_N, int l_x, int r_B, int r_C, int r_N, int r_arg3) {
  int l_i = 0;
  int l_j = 0;
  while (l_i < l_N) {
    l_j = ((l_i * l_B) + l_C);
    l_x = (l_x + l_j);
    l_i = (l_i + 1);
  }
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
  while (((int)(*((unsigned int*)(&r_i)))) < ((int)r_N)) {
    (*((unsigned int*)(&r_x))) = ((*((unsigned int*)(&r_x))) + (*((unsigned int*)(&r_j))));
    (*((unsigned int*)(&r_j))) = ((*((unsigned int*)(&r_j))) + r_B);
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
}