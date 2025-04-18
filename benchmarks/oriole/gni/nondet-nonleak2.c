/* @ELAENIA
 * pre: forall.low_in == exists.low_in;
 * forall: nonleak;
 * exists: nonleak;
 * post: forall.low == exists.low && forall.ret == exists.ret;
 * aspecs: flipCoin() {
 *     pre:  true;
 *     post: ret! == 0 || ret! == 1;
 * }
 * especs:
 *   flipCoin() {
 *     choiceVars: n;
 *     pre:  n == 0 || n == 1;
 *     post: ret! == n;
 * }
 */

int flipCoin();

void nonleak(int low_in, int high_in) {
  int low = low_in;
  int high = high_in;
  if (low < high) {
    low = 0;
  } else {
    low = 1;
  }

  int flip;
  flip = flipCoin();
  if (flip == 0) {
    low = 1 - low;
  }
  int ret = low;
}
