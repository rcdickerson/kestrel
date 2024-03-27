/* @KESTREL
 * pre:   left.a == right.a && left.b == right.b;
 * left:  left;
 * right: right;
 * post:  left.c == right.c;
 */

void left(int a, int b) {
  int c = 0;
  while (a < b) {
   c = c + (a * a);
   a = a + 1;
  }
}

void right(int a, int b) {
  int c = 0;
  while (a < b) {
   c = c + (a * a);
   a = a + 1;
  }
}
