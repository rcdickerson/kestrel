void main(int l_age, int r_age) {
  int l_ret_val = 0;
  if (l_age >= 65) {
    l_ret_val = 20;
  } else {
    if (l_age <= 12) {
      l_ret_val = 50;
    }
  }
  char r_age_var0[4];
  char r_ret_val[4];
  (*((unsigned int*)(&r_age_var0))) = r_age;
  (*((unsigned int*)(&r_ret_val))) = 0;
  if (((int)r_age) < 65) {
    if (((int)r_age) <= 12) {
      (*((unsigned int*)(&r_ret_val))) = 50;
    }
  } else {
    (*((unsigned int*)(&r_ret_val))) = 20;
  }
}