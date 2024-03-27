/* @KESTREL
 * pre: left.o1_scores == right.o2_scores
     && left.o2_scores == right.o1_scores;
 * left: compare;
 * right: compare;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/16809000/how-to-make-the-compareto-method-respect-the-general-contract
 */

float read(int array, int index);
int store(int array, int index, float value);

void _test_gen(int o1_scores, int o2_scores) {
  _main(o1_scores, o2_scores, o2_scores, o1_scores);
}

void compare(int o1_scores, int o2_scores) {
  int ret = -999;

  int comp = 0;
  int i = 0;
  while(i < 5){
    // comp = Double.compare(o1.getScore(i), o2.getScore(i));
    // --
    if (read(o1_scores, i) < read(o2_scores, i)) {
      comp = -1;
    } else if (read(o2_scores, i) < read(o1_scores, i)) {
      comp = 1;
    } else {
      comp = 0;
    }
    // ----
    if (comp!=0) {
      ret = comp;
      break;
    }
    i = i + 1;
  }

  if (ret == -999) ret = 0;
}
