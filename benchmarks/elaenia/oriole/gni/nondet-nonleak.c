/* @ELAENIA
 * pre: forall.low == exists.low;
 * forall: nonleak;
 * exists: nonleak;
 * post: forall.low == exists.low && forall.ret == exists.ret;
 * aspecs: randInt() {
 *     pre:  true;
 *     post: 0 <= ret! && ret! < 100;
 * }
 * especs:
 *   randInt() {
 *     choiceVars: n;
 *     pre:  (0 <= n) && (n < 100);
 *     post: (ret! == n);
 * }
 */

int randInt();

void nonleak(int low, int high) {
  int r;
  r = randInt();
  int ret;
  if (r == 5000) {
    ret = high + low;
  } else {
    ret = low;
  }
}
