#include "seahorn/seahorn.h"

double o1_score[5];
double o2_score[5];

int main() {

  int ret_1 = -999;

  int comp_1 = 0;
  int i_1 = 0;
  while(i_1 < 5){
    // comp = Double.compare(o1.getScore(i), o2.getScore(i));
    // --
    if (o1_score[i_1] < o2_score[i_1]) {
      comp_1 = -1;
    } else if (o2_score[i_1] < o1_score[i_1]) {
      comp_1 = 1;
    } else {
      comp_1 = 0;
    }
    // ----
    if (comp_1!=0) {
      ret_1 = comp_1;
      break;
    }
    i_1 = i_1 + 1;
  }

  if (ret_1 == -999) ret_1 = 0;

  int ret_2 = -999;

  int comp_2 = 0;
  int i_2 = 0;
  while(i_2 < 5){
    // comp = Double.compare(o1.getScore(i), o2.getScore(i));
    // --
    if (o2_score[i_2] < o1_score[i_2]) {
      comp_2 = -1;
    } else if (o1_score[i_2] < o2_score[i_2]) {
      comp_2 = 1;
    } else {
      comp_2 = 0;
    }
    // ----
    if (comp_2!=0) {
      ret_2 = comp_2;
      break;
    }
    i_2 = i_2 + 1;
  }

  if (ret_2 == -999) ret_2 = 0;

  sassert(ret_1 == -ret_2);
}
