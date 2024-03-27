/* @KESTREL
 * pre:   left.low == right.low
       && left.low  > left.h  && left.h  > 0
       && right.low > right.h && right.h > 0;
 * left:  left;
 * right: right;
 * post:  left.y == right.y;
 */

void _test_gen(int low, int l_h, int r_h) {

  if (l_h < 0) { l_h = l_h * -1; }
  l_h = l_h + 1;
  l_h = l_h % 100;

  if (r_h < 0) { r_h = r_h * -1; }
  r_h = r_h + 1;
  r_h = r_h % 100;

  if (low < 0) { low = low * -1; }
  low = low + 1;
  low = low % 100;

  while (low <= l_h || low <= r_h) { low = low * 2; }

  _main(low, l_h, low, r_h);
}

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
