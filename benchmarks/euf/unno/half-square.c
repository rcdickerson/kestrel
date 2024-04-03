/* @KESTREL
 * pre:   left.low == right.low
       && left.low  > left.h  && left.h  > 0
       && right.low > right.h && right.h > 0
       && two_exp(0, 1) == 1
       && (forall x: int, y: int, xp1: int, ypy: int ::
            (two_exp(x, y) == 1 && xp1 == x + 1 && ypy == y + y) ==> (two_exp(xp1, ypy) == 1))
       && (forall x1: int, y1: int, x2: int, y2: int ::
            (two_exp(x1, y1) == 1 && two_exp(x2, y2) == 1) ==> y1 == y2);
 * left:  left;
 * right: right;
 * post:  left.y == right.y;
 */

int two_exp(int x, int y);

void _test_gen(int low, int l_h, int r_h) {
  if (l_h < 0) { l_h = l_h * -1; }
  l_h = (l_h % 100) + 1;

  if (r_h < 0) { r_h = r_h * -1; }
  r_h = (r_h % 100) + 1;

  if (low < 0) { low = low * -1; }
  low = low % 100;

  while (low <= l_h || low <= r_h) { low = low + 5; }

  _main(low, l_h, low, r_h);
}

void left(int low, int h) {
  int i = 0;
  int y = 1;
  int v = 0;
  while (h > i) {
    _invariant("two_exp(left.i, left.y) == 1");
    _invariant("two_exp(right.i, right.y) == 1");
    i = i + 1;
    y = y + y;
  }
  v = 1;
  while (low > i) {
    _invariant("two_exp(left.i, left.y) == 1");
    _invariant("two_exp(right.i, right.y) == 1");
    i = i + 1;
    y = y + y;
  }
}

void right(int low, int h) {
  int i = 0;
  int y = 1;
  int v = 0;
  while (h > i) {
    _invariant("two_exp(left.i, left.y) == 1");
    _invariant("two_exp(right.i, right.y) == 1");
    i = i + 1;
    y = y + y;
  }
  v = 1;
  while (low > i) {
    _invariant("two_exp(left.i, left.y) == 1");
    _invariant("two_exp(right.i, right.y) == 1");
    i = i + 1;
    y = y + y;
  }
}
