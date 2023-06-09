/* @KESTREL
 * pre: for _i in (1..N) { left_o1_score[_i] == right_o2_score[_i] &&
                           left_o2_score[_i] == right_o1_score[_i] };
 * left: left;
 * right: right;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/16809000/how-to-make-the-compareto-method-respect-the-general-contract
 */

const int N = 10;
float left_o1_score[N];
float left_o2_score[N];
float right_o1_score[N];
float right_o2_score[N];

void _generator(int _arr1[N], int _arr2[N]) {
  int _ai1 = 0;
  while (_ai1 < N) {
    left_o1_score[_ai1] = _arr1[_ai1];
    right_o2_score[_ai1] = _arr1[_ai1];
    _ai1 = _ai1 + 1;
  }
  int _ai2 = 0;
  while (_ai2 < N) {
    left_o2_score[_ai2] = _arr2[_ai2];
    right_o1_score[_ai2] = _arr2[_ai2];
    _ai2 = _ai2 + 1;
  }
}

void left(void) {
  int ret = -999;

  int comp = 0;
  int i = 0;
  while(i < 5){
    // comp = Double.compare(o1.getScore(i), o2.getScore(i));
    // --
    if (left_o1_score[i] < left_o2_score[i]) {
      comp = -1;
    } else if (left_o2_score[i] < left_o1_score[i]) {
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

void right(void) {
  int ret = -999;

  int comp = 0;
  int i = 0;
  while(i < 5){
    // comp = Double.compare(o1.getScore(i), o2.getScore(i));
    // --
    if (right_o1_score[i] < right_o2_score[i]) {
      comp = -1;
    } else if (right_o2_score[i] < right_o1_score[i]) {
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
