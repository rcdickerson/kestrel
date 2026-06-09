/* @ELAENIA
 * pre: forall.low == exists.low && forall.low >= 0;
 * pre_sketch: forall.low <= 4;
 * forall: inf_branch_ts;
 * exists: inf_branch_ts;
 * post: forall.x == exists.x;
 * aspecs:
 *  randInt() {
 *    pre:  true;
 *    post: ret! >= 0;
 *  }
 * especs:
 *  randInt() {
 *    choiceVars: n;
 *    pre:  n >= 0;
 *    post: ret! == n;
 *  }
 */

int randInt();
int _randInt() {
  int i = rand();
  if (i < 0) {
    i = i * -1;
  }
  return i;
}

void _test_gen(int low, int high1, int high2) {
  if (low < 0) { low = low * -1; }
  low = low % 100;
  if (high1 < 0) { high1 = high1 * -1; }
  high1 = high1 % 2;
  if (high2 < 0) { high2 = high2 * -1; }
  high2 = high2 % 2;
  _main(low, high1, low, high2);
}

void inf_branch_ts(int low, int high) {
  int x = low;
  int r = 0;
  int max = 0;
  if (high != 0) {
    while (x > 0) {
      _invariant("left.x >= 0");
      _invariant("right.x >= 0");
      r = randInt();
      if (r < 1) {
        max = 1;
      } else {
        max = r;
      }
      if (max >= x) {
        x = 0;
      } else {
        x = x - max;
      }
    }
  } else {
    while (x > 0) {
      _invariant("left.x >= 0");
      _invariant("right.x >= 0");
      x = x - 1;
    }
  }
}
