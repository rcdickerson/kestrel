/* @ELAENIA
 * pre: true;
 * forall: refinement;
 * exists: original;
 * post: forall.ret == exists.ret;
 * aspecs: flipCoin() {
 *     pre:  true;
 *     post: (ret! == 0) || (ret! == 1);
 * }
 * especs:
 *   flipCoin() {
 *     choiceVars: n;
 *     pre:  (n == 0) || (n == 1);
 *     post: (ret! == n);
 * }
 */

int flipCoin();

void original() {
  int r;
  r = flipCoin();
  int ret = 0;
  if (r == 0) {
    ret = 10;
  } else {
    ret = 20;
  }
}

void refinement() {
  int r;
  r = flipCoin();
  int ret = 0;
  if (r == 0) {
    ret = 20;
  } else {
    ret = 10;
  }
}
