/* @KESTREL
 * pre:   left.n == right.n;
 * left:  f0;
 * right: f1;
 * post:  left.x == right.x;
 */

void f0(int n) {
  int x, i;

  i = 0; x = 0;
  while (i <= n) {
    x = x + i;
    i = i + 1;
  }
}

void f1(int n) {
  int x, j;

  j = 1; x = 0;
  while (j <= n) {
    x = x + j;
    j = j + 1;
  }
}
