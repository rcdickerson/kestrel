/* @ELAENIA
 * pre: true;
 * forall: E1;
 * exists: E2;
 * post: forall.y == exists.z;
 * aspecs: any() {
 *     pre:  true;
 *     post: true;
 * }
 * especs:
 *   any() {
 *     choiceVars: n;
 *     pre:  true;
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
