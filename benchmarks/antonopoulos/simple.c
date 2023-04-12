/* @KESTREL
 * pre:   1.N == 2.N;
 * left:  fun;
 * right: fun;
 * post:  1.x == 2.x;
 */

void fun(int N) {
  int x = 0;
  int i = 0;

  while( i <= N ) {
    x = x + 1;
    i = i + 1;
  }
}
