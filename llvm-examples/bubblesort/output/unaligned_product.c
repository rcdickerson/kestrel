void main(float l_a[10], void* r_a) {
  int l_i = 0;
  while (l_i < 10) {
    int l_j = (10 - 1);
    while (l_j > l_i) {
      if (l_a[l_j - 1] > l_a[l_j]) {
        float l_temp = l_a[l_j];
        l_a[l_j] = l_a[l_j - 1];
        l_a[l_j - 1] = l_temp;
      }
      l_j = (l_j - 1);
    }
    l_i = (l_i + 1);
  }
  char r_temp[4];
  char r_n[8];
  char r_a_var2[8];
  char r_j[8];
  char r_i[8];
  long r_val5;
  long r_val6;
  long r_val7;
  float r_val8;
  long r_val9;
  long r_val10;
  long r_val11;
  (*((void**)(&r_a_var2))) = r_a;
  (*((unsigned long*)(&r_n))) = 10;
  (*((unsigned long*)(&r_i))) = 0;
  if ((*((unsigned long*)(&r_i))) >= 10) {
  } else {
    (*((unsigned long*)(&r_j))) = 9;
  }
  if (((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) <= (*((unsigned long*)(&r_i))))) {
    (*((unsigned long*)(&r_i))) = ((*((unsigned long*)(&r_i))) + 1);
  }
  if (((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) {
    r_val5 = ((*((unsigned long*)(&r_j))) - 1);
  }
  if ((((*((unsigned long*)(&r_i))) < 10) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val5 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val5, 10, &r_alloc_d10824f57abd82b96f74d8a998900e37);
  }
  if ((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) {
    r_val6 = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && (r_val6 >= 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 10, &r_alloc_c1472aaa99a0c9e01c4370a339afe9b1);
  }
  if ((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) {
    r_val7 = (*((unsigned long*)(&r_j)));
  }
  if (((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val7 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val7, 10, &r_alloc_b306f3c5835633be8c030b2750cb09fc);
  }
  if (((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (r_val7 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) {
    r_val8 = ((float*)r_a)[r_val7];
    (*((float*)(&r_temp))) = r_val8;
    r_val9 = ((*((unsigned long*)(&r_j))) - 1);
  }
  if ((((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (r_val7 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val9 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val9, 10, &r_alloc_a026c78e675b1169ca6570e96453f0ba);
  }
  if ((((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (r_val7 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val9 < 10)) {
    r_val10 = (*((unsigned long*)(&r_j)));
  }
  if (((((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (r_val7 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val9 < 10)) && (r_val10 >= 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val10, 10, &r_alloc_991cfbf1566089e55fc7fedefbf4d17b);
  }
  if (((((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (r_val7 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val9 < 10)) && (r_val10 < 10)) {
    ((float*)r_a)[r_val10] = ((float*)r_a)[r_val9];
    r_val11 = ((*((unsigned long*)(&r_j))) - 1);
  }
  if ((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val11 >= 10)) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (r_val7 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val9 < 10)) && (r_val10 < 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val11, 10, &r_alloc_a660e85f91318953292432dd99f84179);
  }
  if ((((((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && (r_val7 < 10)) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val9 < 10)) && (r_val10 < 10)) && (r_val11 < 10)) {
    ((float*)r_a)[r_val11] = r_val8;
  }
  if ((((((*((unsigned long*)(&r_i))) < 10) && (r_val5 < 10)) && ((*((unsigned long*)(&r_j))) > (*((unsigned long*)(&r_i))))) && (r_val6 < 10)) && ((((float*)r_a)[r_val5] <= ((float*)r_a)[r_val6]) || (((((r_val7 < 10) && (((float*)r_a)[r_val5] > ((float*)r_a)[r_val6])) && (r_val9 < 10)) && (r_val10 < 10)) && (r_val11 < 10)))) {
    (*((unsigned long*)(&r_j))) = ((*((unsigned long*)(&r_j))) - 1);
  }
}