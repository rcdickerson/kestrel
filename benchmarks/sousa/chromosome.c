/* @KESTREL
 * pre: for _i in (1..10) { left.o1_score[_i] == right.o2_score[_i] &&
                            left.o2_score[_i] == right.o1_score[_i] };
 * left: left;
 * right: right;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/16809000/how-to-make-the-compareto-method-respect-the-general-contract
 */

#define N 10

void _generator(int _arr1[N], int _arr2[N]) {
  int _ai1 = 0;
  float l_o1_score[N];
  float r_o1_score[N];
  float l_o2_score[N];
  float r_o2_score[N];
  while (_ai1 < N) {
    l_o1_score[_ai1] = _arr1[_ai1];
    r_o2_score[_ai1] = _arr1[_ai1];
    _ai1 = _ai1 + 1;
  }
  int _ai2 = 0;
  while (_ai2 < N) {
    l_o2_score[_ai2] = _arr2[_ai2];
    r_o1_score[_ai2] = _arr2[_ai2];
    _ai2 = _ai2 + 1;
  }
}

void left(float o1_score[N], float o2_score[N]) {
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

void right(float o1_score[N], float o2_score[N]) {
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
