/* @KESTREL
 * pre:   left.f11 == right.f21
       && left.f12 == right.f22
       && left.n1  == right.n2
       && left.k1  == right.k2
       && left.l1  == right.l2;
 * left:  left;
 * right: right;
 * post:  left.l1 == right.l2;
 */

void _generator(int f1, int f2, int n, int k, int l) {
  int l_f11 = f1;
  int r_f21 = f1;
  int l_f12 = f2;
  int r_f22 = f2;
  int l_n1 = n;
  int r_n2 = n;
  int l_k1 = k;
  int r_k2 = k;
  int l_l1 = l;
  int r_l2 = l;
}

void left(int f11, int f12, int n1, int k1, int l1) {
 while(n1 > 0) {
	f11 = f11 + f12;
	f12 = f11 - f12;
	n1 = n1 - 1;
    }
    if (f11 > k1) {
	l1 = 1;
    } else {
	l1 = 0;
    }
}

void right(int f21, int f22, int n2, int k2, int l2) {
   while(n2 > 0) {
	f21 = f21 + f22;
	f22 = f21 - f22;
	n2 = n2 - 1;
    }
    if (f21 > k2) {
	l2 = 1;
    } else {
	l2 = 0;
    }
}
