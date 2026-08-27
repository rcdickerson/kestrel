void main(int l_a, int l_b, int r_arg0, int r_b) {
  int l_c = 0;
  while (l_a < l_b) {
    l_c = (l_c + (l_a * l_a));
    l_a = (l_a + 1);
  }
  char r_b_var0[4];
  char r_c[4];
  char r_a[4];
  (*((unsigned int*)(&r_a))) = r_arg0;
  (*((unsigned int*)(&r_b_var0))) = r_b;
  (*((unsigned int*)(&r_c))) = 0;
  while (((int)(*((unsigned int*)(&r_a)))) < ((int)r_b)) {
    (*((unsigned int*)(&r_c))) = ((*((unsigned int*)(&r_c))) + ((*((unsigned int*)(&r_a))) * (*((unsigned int*)(&r_a)))));
    (*((unsigned int*)(&r_a))) = ((*((unsigned int*)(&r_a))) + 1);
  }
}