/* @ELAENIA
 * pre: forall.param1A == exists.param1A
     && forall.param2A != exists.param2A
     && forall.param1B != exists.param1B
     && forall.param2B == exists.param2B;
 * forall: unused;
 * exists: unused;
 * post: forall.retA == exists.retA
      || forall.retB == exists.retB;
 * aspecs: flip() {
 *     pre:  true;
 *     post: ret! == 0 || ret! == 1;
 * }
 * especs: flip() {
 *     choiceVars: n;
 *     pre:  n == 0 || n == 1;
 *     post: ret! == n;
 * }
 */

int flip();

void unused(int param1A, int param2A, int param1B, int param2B) {
  int xA = param1A + param2A;
  int rA;
  rA = flip();
  int retA;
  if (rA == 0) {
    retA = xA - param2A;
  } else {
    retA = param1A;
  }

  int xB = param1B + param2B;
  int rB;
  rB = flip();
  int retB;
  if (rB == 0) {
    retB = xB - param2B;
  } else {
    retB = param1B;
  }
}
