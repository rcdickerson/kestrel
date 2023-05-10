/* @KESTREL
 * pre:   left.o1 == right.o1 &&
          left.o1_getCardSet == right.o1_getCardSet &&
          left.o1_getCardRarity == right.o1_getCardRarity &&
          left.o1_getCardId == right.o1_getCardId &&
          left.o1_cardType == right.o1_cardType &&
          left.o2 == right.o2 &&
          left.o2_getCardSet == right.o2_getCardSet &&
          left.o2_getCardRarity == right.o2_getCardRarity &&
          left.o2_getCardId == right.o2_getCardId &&
          left.o2_cardType == right.o2_cardType;
 * left:  left;
 * right: right;
 * post:  left.ret == right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/11441666/java-error-comparison-method-violates-its-general-contract
 */

void left(int o1, int o1_getCardSet, int o1_getCardRarity, int o1_getCardId, int o1_cardType,
          int o2, int o2_getCardSet, int o2_getCardRarity, int o2_getCardId, int o2_cardType) {

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

}

void right(int o1, int o1_getCardSet, int o1_getCardRarity, int o1_getCardId, int o1_cardType,
           int o2, int o2_getCardSet, int o2_getCardRarity, int o2_getCardId, int o2_cardType) {
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
}
