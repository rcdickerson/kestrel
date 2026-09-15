void main(int l_x, int r_x) {
  int l_y = 0;
  int l_z = (2 * l_x);
  int l_i = 0;
  while (l_i < l_z) {
    l_y = (l_y + l_x);
    l_i = (l_i + 1);
  }
  char r_z[4];
  char r_i[4];
  char r_y[4];
  (*((unsigned int*)(&r_z))) = r_x;
  (*((unsigned int*)(&r_y))) = 0;
  (*((unsigned int*)(&r_i))) = 0;
  while (((int)(*((unsigned int*)(&r_i)))) < ((int)r_x)) {
    (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + r_x);
    (*((unsigned int*)(&r_i))) = ((*((unsigned int*)(&r_i))) + 1);
  }
  (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) * 2);
}