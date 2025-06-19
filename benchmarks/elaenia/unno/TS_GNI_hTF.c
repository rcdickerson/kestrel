/* @ELAENIA
 * pre: forall.low == exists.low && forall.high == 1 && exists.high == 0;
 * forall: ti_gni;
 * exists: ti_gni;
 * post: forall.ret == exists.ret;
 * aspecs:
 *  arb_bool() {
 *    pre:  true;
 *    post: ret! == 0 || ret! == 1;
 *  }
 *  arb_int() {
 *    pre:  true;
 *    post: true;
 *  }
 * especs:
 *  arb_bool() {
 *    choiceVars: n;
 *    pre:  n == 0 || n == 1;
 *    post: (ret! == n);
 *  }
 *  arb_int() {
 *    choiceVars: n;
 *    pre: true;
 *    post: (ret! == n);
 *  }
 */

int arb_bool();
int _arb_bool() {
  return rand() % 2;
}

int arb_int();
int _arb_int() {
  return rand() % 10;
}

void _test_gen(int low, int high1, int high2) {
  if (low < 0) {
    low = (low * (-1));
  }
  low = (low % 10);
  _main(low, 1, low, 0);
}

void ti_gni(int low, int high) {
  int ret;
  int x;
  int r = 0;
  if (high != 0) {
    x = arb_int();
    if (x >= low) {
      ret = x;
    } else {
      while (1 == 1) { x = x; }
    }
  } else {
    x = low;
    r = arb_bool();
    while ( r != 0 ) {
      x = x + 1;
      r = arb_bool();
    }
    ret = x;
  }
}
