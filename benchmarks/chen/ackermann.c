/* @KESTREL
 * pre:   left.m == right.m && left.n == right.n;
 * left:  f0;
 * right: f1;
 * post:  left.ret == right.ret;
 */

void f0(int m, int n) {
  int result = f0rec(m, n);
}

void f1(int m, int n) {
  int result = f1rec(m, n);
}

int f0rec(int m, int n) {
  if (m == 0) {
    return n + 1;
  } else {
    if (m > 0 && n == 0) {
        return f0rec(m - 1, 1);
    } else {
        int x = f0rec(m, n - 1);
        return f0rec(m - 1, x);
    }
  }
}

int f1rec(int m, int n) {
  if (m > 0 && n == 0) {
    return f1rec(m - 1, 1);
  } else {
    if (m == 0) {
      return n + 1;
    } else {
      int x = f1rec(m, n - 1);
      return f1rec(m - 1, x);
    }
  }
}
