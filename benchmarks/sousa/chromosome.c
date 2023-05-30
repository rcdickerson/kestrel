/* @KESTREL
 * pre: for _i in 1..5 { left.o1_score[_i] == right.o2_score[_i] &&
                         left.o2_score[_i] == right.o1_score[_i] };
 * left: cmp;
 * right: cmp;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/16809000/how-to-make-the-compareto-method-respect-the-general-contract
 */

void cmp(float o1_score[5], float o2_score[5]) {
  int ret = -999;

  int comp = 0;
  int i = 0;
  while(i < 5){
    // comp = Double.compare(o1.getScore(i), o2.getScore(i));
    // --
    if (o1_score[i] < o2_score[i]) {
      comp = -1;
    } else if (o2_score[i] < o1_score[i]) {
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
