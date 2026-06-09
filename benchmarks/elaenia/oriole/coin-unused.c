/* @ELAENIA
 * pre: forall.param1A == exists.param1A
     && forall.param2A != exists.param2A
     && forall.param1B != exists.param2B
     && forall.param2B == exists.param2B;
 * forall: unused;
 * exists: unused;
 * post: forall.rA == exists.rA
      || forall.rB == exists.rB;
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
  int rA;
  rA = flip();

  int rB;
  rB = flip();
}
