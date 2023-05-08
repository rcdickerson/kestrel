/* @KESTREL
 * pre:   left.N == right.N;
 * left:  fun;
 * right: fun;
 * post:  left.x == right.x;
 */

void fun(int N) {
  int x = 0;
  int i = 0;

  while( i <= N ) {
    x = x + 1;
    i = i + 1;
  }
}
