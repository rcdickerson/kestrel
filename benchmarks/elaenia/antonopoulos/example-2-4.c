/* @ELAENIA
 * pre: true;
 * forall: E1;
 * exists: E2;
 * post: forall.y == exists.z;
 * aspecs: any() {
 *     pre:  true;
 *     post: ret! >= 0;
 * }
 * especs:
 *   any() {
 *     choiceVars: n;
 *     pre:  n >= 0;
 *     post: ret! == n;
 * }
 */

int any();
int _any() {
  int x = rand();
  if (x < 0) { x = x * -1; }
  return x;
}

void E1() {
  int x;
  int y;
  x = any();
  y = x;
}

void E2() {
  int t;
  int z;
  t = any();
  z = t + 1;
}
