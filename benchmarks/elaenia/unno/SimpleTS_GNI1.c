/* @ELAENIA
 * pre: forall.low == exists.low;
 * forall: simple_ts;
 * exists: simple_ts;
 * post: forall.ret == exists.ret;
 * aspecs:
 *  flip() {
 *    pre:  true;
 *    post: ret! == 0 || ret! == 1;
 *  }
 * especs:
 *  flip() {
 *    choiceVars: n;
 *    pre:  n == 0 || n == 1;
 *    post: (ret! == n);
 *  }
 */

int flip();

int _flip() {
  return rand() % 2;
}

void _test_gen(int low, int high1, int high2) {
  if (low < 0) { low = low * -1; }
  low = low % 100;
  if (high1 < 0) { high1 = high1 * -1; }
  high1 = high1 % 5;
  if (high2 < 0) { high2 = high2 * -1; }
  high2 = high2 % 5;
  _main(low, high1, low, high2);
}

void simple_ts(int low, int high) {
  int x = low;
  int r;
  r = flip();
  while ( r != 0 ) {
    x = x + 1;
    r = flip();
  }
  int ret = (high + x);
}
