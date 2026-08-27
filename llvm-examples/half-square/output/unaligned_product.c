void main(int l_low, int l_h, int r_low, int r_h) {
  int l_i = 0;
  int l_y = 0;
  int l_v = 0;
  while (l_h > l_i) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
  l_v = 1;
  while (l_low > l_i) {
    l_i = (l_i + 1);
    l_y = (l_y + l_y);
  }
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
  while (((int)r_h) > ((int)(*((unsigned int*)(&r_i))))) {
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + (*((unsigned int*)(&r_y))));
  }
  (*((unsigned int*)(&r_v))) = 1;
  while (((int)r_low) > ((int)(*((unsigned int*)(&r_i))))) {
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
    (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + (*((unsigned int*)(&r_y))));
  }
}