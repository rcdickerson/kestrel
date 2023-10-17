/* @KESTREL
 * pre:   left.f11 == right.f21
       && left.f12 == right.f22
       && left.n1  == right.n2
       && left.l1  == right.l2
       && left.x1  == right.x2
       && left.i1  == right.i2;
 * left:  left;
 * right: right;
 * post:  left.l1 == right.l2;
 */

void _generator(int f1, int f2, int n, int l, int x, int i) {
  int l_f11 = f1;
  int r_f21 = f1;
  int l_f12 = f2;
  int r_f22 = f2;
  int l_n1 = n;
  int r_n2 = n;
  int l_l1 = l;
  int r_l2 = l;
  int l_x1 = x;
  int r_x2 = x;
  int l_i1 = i;
  int r_i2 = i;
}

void left(int f11, int f12, int n1, int l1, int x1, int i1, int h1) {
  while(n1 > 0) {
	f11 = f11 + f12;
	f12 = f11 - f12;
	n1 = n1 - 1;
    }
    if (h1) {
	x1 = 1;
    }
    if (!h1) {
	x1 = 1;
    }
    while(i1 < f11) {
	l1 = l1 + x1;
	i1 = i1 + 1;
    }
}

void right(int f21, int f22, int n2, int l2, int x2, int i2, int h2) {
while(n2 > 0) {
	f21 = f21 + f22;
	f22 = f21 - f22;
	n2 = n2 - 1;
    }
    if (h2) {
	x2 = 1;
    }
    if (!h2) {
	x2 = 1;
    }
    while(i2 < f21) {
	l2 = l2 + x2;
	i2 = i2 + 1;
    }
}
