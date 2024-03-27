/* @KESTREL
 * pre:   left.low == right.low
       && left.low  > left.h  && left.h  > 0
       && right.low > right.h && right.h > 0;
 * left:  left;
 * right: right;
 * post:  left.y == right.y;
 */

void left(int low, int h) {
  int i = 0;
  int y = 0;
  int v = 0;
  while (h > i) {
    i = i + 1;
    y = y + y;
  }
  v = 1;
  while (low > i) {
    i = i + 1;
    y = y + y;
  }
}

void right(int low, int h) {
  int i = 0;
  int y = 0;
  int v = 0;
  while (h > i) {
    i = i + 1;
    y = y + y;
  }
  v = 1;
  while (low > i) {
    i = i + 1;
    y = y + y;
  }
}
