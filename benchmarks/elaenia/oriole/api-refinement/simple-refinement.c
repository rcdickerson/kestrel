/* @ELAENIA
 * pre: true;
 * forall: refinement;
 * exists: original;
 * post: forall.x == exists.x;
 * aspecs: refinedRand() {
 *     pre:  true;
 *     post: (ret! >= 0) && (ret! < 20) && (ret! % 2 == 1);
 * }
 * especs:
 *   originalRand() {
 *     choiceVars: n;
 *     pre:  (n >= 0) && (n < 20);
 *     post: (ret! == n);
 * }
 */

int originalRand();
int refinedRand();

void original() {
  int x;
  x = originalRand();
}

void refinement() {
  int x;
  x = refinedRand();
}
