void main(int l_x, int r_x) {
  int l_z = 0;
  int l_y = 0;
  l_z = (2 * l_x);
  while (l_z > 0) {
    l_z = (l_z - 1);
    l_y = (l_y + l_x);
  }
  char r_x_var0[4];
  char r_y[4];
  char r_z[4];
  (*((unsigned int*)(&r_x_var0))) = r_x;
  (*((unsigned int*)(&r_z))) = (2 * r_x);
  (*((unsigned int*)(&r_y))) = 0;
  while (((int)(*((unsigned int*)(&r_z)))) > 0) {
    (*((unsigned int*)(&r_z))) = ((*((unsigned int*)(&r_z))) - 1);
    (*((unsigned int*)(&r_y))) = ((*((unsigned int*)(&r_y))) + r_x);
  }
}