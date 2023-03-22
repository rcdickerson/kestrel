/*
 * Based on http://stackoverflow.com/questions/11441666/java-error-comparison-method-violates-its-general-contract
 *
 */

//#include "seahorn/seahorn.h"
//extern int arb_int(void);

int main() {
   int o1 = arb_int();
	 int o1_getCardSet = arb_int();
   int o1_getCardRarity = arb_int();
   int o1_getCardId = arb_int();
   int o1_cardType = arb_int();

   int o2 = arb_int();
	 int o2_getCardSet = arb_int();
   int o2_getCardRarity = arb_int();
   int o2_getCardId = arb_int();
   int o2_cardType = arb_int();

   rel_left();

     int ret_1;

     if (o1 == o2){
       ret_1 = 0;
     }
		 else if (o1_getCardSet > o2_getCardSet) {
		     ret_1 =  1;
		 }
		 else if (o1_getCardSet < o2_getCardSet) {
		     ret_1 =  -1;
		 }
		 else if (o1_getCardRarity < o2_getCardRarity) {
		     ret_1 =  1;
		 }
		 else if (o1_getCardRarity > o2_getCardRarity) {
		     ret_1 =  -1;
		 }
		 else if (o1_getCardId > o2_getCardId) {
		     ret_1 =  1;
		 }
		 else if (o1_getCardId < o2_getCardId) {
		     ret_1 =  -1;
		 } else {
       ret_1 =  o1_cardType - o2_cardType;  //watch out for overflow!
     }

   rel_mid();

     int ret_2;

     if (o2 == o1){
       ret_2 = 0;
     }
		 else if (o2_getCardSet > o1_getCardSet) {
		     ret_2 = 1;
		 }
		 else if (o2_getCardSet < o1_getCardSet) {
		     ret_2 = -1;
		 }
		 else if (o2_getCardRarity < o1_getCardRarity) {
		     ret_2 = 1;
		 }
		 else if (o2_getCardRarity > o1_getCardRarity) {
		     ret_2 = -1;
		 }
		 else if (o2_getCardId > o1_getCardId) {
		     ret_2 = 1;
		 }
		 else if (o2_getCardId < o1_getCardId) {
		     ret_2 = -1;
		 } else {
       ret_2 = o2_cardType - o1_cardType;  //watch out for overflow!
     }

   rel_right();

//   sassert(ret_1 == -ret_2);

}
