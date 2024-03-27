/* @KESTREL
 * pre:   left.n == right.n && left.n > 0 && left.n < 100000;
 * left:  left;
 * right: right;
 * post:  left.x == right.y;
 */

void left(int n) {
  int x = 0;
  int i = 0;
    while (i <= n) {
	x = x + i;
	i = i + 1;
    }
}

void right(int n) {
  int y = 0;
  int j = 1;
    while (j <= n) {
	y = y + j;
	j = j + 1;
    }
}
