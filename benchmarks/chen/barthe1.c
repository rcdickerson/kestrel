/* @KESTREL
 * pre:   left.n == right.n && left.c == right.c;
 * left:  f0;
 * right: f1;
 * post:  left.x == right.x;
 */

void f0(int n, int c) {
  int x, i, j;

  i = 0; j = 0; x = 0;
  while (i < n) {
    j = 5 * i + c;
    x = x + j;
    i = i + 1;
  }
}

void f1(int n, int c) {
  int x, i, j;

  i = 0; j = c; x = 0;
  while (i < n) {
    x = x + j;
    j = j + 5;
    i = i + 1;
  }
}
