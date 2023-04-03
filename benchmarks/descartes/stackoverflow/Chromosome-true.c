/*
 * Based on http://stackoverflow.com/questions/16809000/how-to-make-the-compareto-method-respect-the-general-contract
 *
 */

//#include "seahorn/seahorn.h"
//extern int arb_int(void);
//extern double arb_double(void);

int main() {
  int getScore(int num);
  int isNull;

  int o1_isNull = arb_int();
  double o1_score[5];

  int o2_isNull = arb_int();
  int o2_score[5] = {
    arb_double(),
    arb_double(),
    arb_double(),
    arb_double(),
    arb_double()
  };

  rel_left();

  int ret_1 = -999;

//  if(o2_isNull == 0) {
//    ret_1 = 1;
//  } else {
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
//  }

  rel_mid();

  int ret_2 = -999;

//  if(o1_isNull == 0) {
//    ret_2 = 1;
//  } else {
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
//  }

  rel_right();

//  sassert(ret_1 = -ret_2);
}
