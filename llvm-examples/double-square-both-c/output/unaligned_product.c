void main(int l_x, int r_x) {
  int l_z = 0;
  int l_y = 0;
  l_z = (2 * l_x);
  while (l_z > 0) {
    l_z = (l_z - 1);
    l_y = (l_y + l_x);
  }
  int r_z = 0;
  int r_y = 0;
  r_z = (2 * r_x);
  while (r_z > 0) {
    r_z = (r_z - 1);
    r_y = (r_y + r_x);
  }
}