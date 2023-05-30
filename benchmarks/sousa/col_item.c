/* @KESTREL
 * pre:   left.o1 == right.o2 &&
          left.o1_getCardSet == right.o2_getCardSet &&
          left.o1_getCardRarity == right.o2_getCardRarity &&
          left.o1_getCardId == right.o2_getCardId &&
          left.o1_cardType == right.o2_cardType;
 * left:  cmp;
 * right: cmp;
 * post:  left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/11441666/java-error-comparison-method-violates-its-general-contract
 */

void cmp(int o1, int o1_getCardSet, int o1_getCardRarity, int o1_getCardId, int o1_cardType,
         int o2, int o2_getCardSet, int o2_getCardRarity, int o2_getCardId, int o2_cardType) {

     int ret;

     if (o1 == o2){
       ret = 0;
     }
		 else if (o1_getCardSet > o2_getCardSet) {
		     ret =  1;
		 }
		 else if (o1_getCardSet < o2_getCardSet) {
		     ret =  -1;
		 }
		 else if (o1_getCardRarity < o2_getCardRarity) {
		     ret =  1;
		 }
		 else if (o1_getCardRarity > o2_getCardRarity) {
		     ret =  -1;
		 }
		 else if (o1_getCardId > o2_getCardId) {
		     ret =  1;
		 }
		 else if (o1_getCardId < o2_getCardId) {
		     ret =  -1;
		 } else {
       ret =  o1_cardType - o2_cardType;  //watch out for overflow!
     }

}
