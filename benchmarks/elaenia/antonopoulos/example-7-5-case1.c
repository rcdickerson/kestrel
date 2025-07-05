/* @ELAENIA
 * pre: forall.l == exists.l && forall.l >= 0
     && forall.h > forall.l;
 * forall: example;
 * exists: example;
 * post: forall.o == exists.o;
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

void example(int l, int h) {
  int a1;
  int a2;
  int x = 0;
  int o = 0;

  a1 = any();
  a2 = any();
  if (h > l) {
    o = l + a1;
  } else {
    x = a2;
    if (x > l) {
      o = x;
    } else {
      o = l;
    }
  }
}
