/* @KESTREL
 * pre:   left.n == right.n;
 * left:  fun;
 * right: fun;
 * post:  left.x == right.x;
 */

void fun(int n) {
  int x = 0;
  int i = 0;

  while( i <= n ) {
    x = x + 1;
    i = i + 1;
  }
}
