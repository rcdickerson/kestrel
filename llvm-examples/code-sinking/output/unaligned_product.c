void main(int l_a[10 + 1], void* r_a) {
  int l_max = l_a[0];
  int l_maxi = 0;
  int l_i = 0;
  while (l_i < 10) {
    if (l_max < l_a[l_i]) {
      l_max = l_a[l_i];
      l_maxi = l_i;
    }
    l_i = (l_i + 1);
  }
  int l_t = l_a[10];
  l_a[10] = l_max;
  l_a[l_maxi] = l_t;
  char r_t[4];
  char r_n[8];
  char r_a_var2[8];
  char r_maxi[8];
  char r_max[4];
  char r_j[8];
  long r_val6;
  long r_val7;
  int r_val8;
  long r_val9;
  (*((void**)(&r_a_var2))) = r_a;
  (*((unsigned long*)(&r_n))) = 10;
  (*((unsigned long*)(&r_j))) = 0;
  (*((unsigned int*)(&r_max))) = 0;
  (*((unsigned long*)(&r_maxi))) = 0;
  if ((*((unsigned long*)(&r_j))) >= 10) {
  } else {
    if ((*((unsigned long*)(&r_j))) == 0) {
      (*((unsigned int*)(&r_max))) = (*((unsigned int*)r_a));
      (*((unsigned long*)(&r_maxi))) = 0;
    }
    r_val6 = (*((unsigned long*)(&r_j)));
  }
  if (((*((unsigned long*)(&r_j))) < 10) && (r_val6 >= 11)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val6, 11, &r_alloc_b6a9a667e486e61363affc1a8f96404f);
  }
  if ((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (((int)(*((unsigned int*)(&r_max)))) < ((int)((unsigned int*)r_a)[r_val6]))) {
    r_val7 = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && (r_val7 >= 11)) && (((int)(*((unsigned int*)(&r_max)))) < ((int)((unsigned int*)r_a)[r_val6]))) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val7, 11, &r_alloc_25839b1997cb2d6209d8d3c6ba0567b5);
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val7 < 11)) && (r_val6 < 11)) && (((int)(*((unsigned int*)(&r_max)))) < ((int)((unsigned int*)r_a)[r_val6]))) {
    (*((unsigned int*)(&r_max))) = ((unsigned int*)r_a)[r_val7];
    (*((unsigned long*)(&r_maxi))) = (*((unsigned long*)(&r_j)));
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && ((*((unsigned long*)(&r_j))) == 10)) {
    r_val8 = ((unsigned int*)r_a)[10];
    (*((unsigned int*)(&r_t))) = r_val8;
    ((unsigned int*)r_a)[10] = (*((unsigned int*)(&r_max)));
    r_val9 = (*((unsigned long*)(&r_maxi)));
  }
  if ((((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val9 >= 11)) && ((*((unsigned long*)(&r_j))) == 10)) {
    r__RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(r_val9, 11, &r_alloc_f8b2f46ae7d9d9573fbd43ab55b46be9);
  }
  if ((((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (r_val9 < 11)) && ((*((unsigned long*)(&r_j))) == 10)) {
    ((unsigned int*)r_a)[r_val9] = r_val8;
  }
  if (((((*((unsigned long*)(&r_j))) < 10) && (r_val6 < 11)) && ((r_val7 < 11) || (((int)(*((unsigned int*)(&r_max)))) >= ((int)((unsigned int*)r_a)[r_val6])))) && (((*((unsigned long*)(&r_j))) != 10) || (r_val9 < 11))) {
    (*((unsigned long*)(&r_j))) = ((*((unsigned long*)(&r_j))) + 1);
  }
}