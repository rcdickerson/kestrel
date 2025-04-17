/* @ELAENIA
 * pre: exists.handValue_in >= 2 && exists.handValue_in <= 20;
 * forall: noop;
 * exists: play;
 * post: exists.handValue == 21;
 * aspecs:
 *   draw() {
 *     pre:  true;
 *     post: ret! >= 1 && ret! <= 10;
 *   }
 * especs:
 *   draw() {
 *     choiceVars: n;
 *     pre:  (n >= 1) && (n <= 10);
 *     post: (ret! == n);
 *   }
 */

void _test_gen(int handValue) {
  if (handValue < 0) { handValue = handValue * -1; }
  handValue = (handValue % 19) + 2;
  _main(handValue);
}

int draw();

void noop() {
  int x = 0;
}

void play(int handValue_in) {
  int handValue = handValue_in;
  while (handValue < 21) {
    _invariant("exists.handValue <= 21");
    int card;
    card = draw();
    handValue = handValue + card;
  }
}
