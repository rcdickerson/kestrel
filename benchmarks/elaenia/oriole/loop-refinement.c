/* @ELAENIA
 * pre: true;
 * forall: refinement;
 * exists: original;
 * post: forall.sum == exists.sum;
 * aspecs: randOdd() {
 *     pre:  true;
 *     post: (0 <= ret!) && (ret! < 10) && (ret! % 2 == 1);
 * }
 * especs:
 *   rand() {
 *     choiceVars: n;
 *     pre:  (0 <= n) && (n < 10);
 *     post: (ret! == n);
 * }
 */

int rand();
int randOdd();

void original() {
  int sum = 0;
  int i = 0;
  while (sum <= 100) {
    _invariant("l_sum == r_sum");
    int r;
    r = rand();
    sum = sum + r + 1;
    if (i > 5) { assume(sum > 100); }
    i = i + 1;
  }
}

void refinement() {
  int sum = 0;
  int i = 0;
  while (sum <= 100) {
    int r;
    r = randOdd();
    sum = sum + r + 1;
    if (i > 5) { assume(sum > 100); }
    i = i + 1;
  }
}
