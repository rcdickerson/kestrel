/* @KESTREL
 * pre:   left_o1 == right_o2 &&
          left_o1_getCardSet == right_o2_getCardSet &&
          left_o1_getCardRarity == right_o2_getCardRarity &&
          left_o1_getCardId == right_o2_getCardId &&
          left_o1_cardType == right_o2_cardType &&
          left_o2 == right_o1 &&
          left_o2_getCardSet == right_o1_getCardSet &&
          left_o2_getCardRarity == right_o1_getCardRarity &&
          left_o2_getCardId == right_o1_getCardId &&
          left_o2_cardType == right_o1_cardType;
 * left:  left;
 * right: right;
 * post:  left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/11441666/java-error-comparison-method-violates-its-general-contract
 */

int left_o1; int left_o1_getCardSet; int left_o1_getCardRarity; int left_o1_getCardId; int left_o1_cardType;
int left_o2; int left_o2_getCardSet; int left_o2_getCardRarity; int left_o2_getCardId; int left_o2_cardType;

int right_o1; int right_o1_getCardSet; int right_o1_getCardRarity; int right_o1_getCardId; int right_o1_cardType;
int right_o2; int right_o2_getCardSet; int right_o2_getCardRarity; int right_o2_getCardId; int right_o2_cardType;


void _test_gen(int _o1, int _cardSet1, int _cardRarity1, int _cardId1, int _cardType1,
               int _o2, int _cardSet2, int _cardRarity2, int _cardId2, int _cardType2) {
  left_o1 = _o1;
  left_o1_getCardSet = _cardSet1;
  left_o1_getCardRarity = _cardRarity1;
  left_o1_getCardId = _cardId1;
  left_o1_cardType = _cardType1;

  left_o2 = _o2;
  left_o2_getCardSet = _cardSet2;
  left_o2_getCardRarity = _cardRarity2;
  left_o2_getCardId = _cardId2;
  left_o2_cardType = _cardType2;

  right_o1 = _o2;
  right_o1_getCardSet = _cardSet2;
  right_o1_getCardRarity = _cardRarity2;
  right_o1_getCardId = _cardId2;
  right_o1_cardType = _cardType2;

  right_o2 = _o1;
  right_o2_getCardSet = _cardSet1;
  right_o2_getCardRarity = _cardRarity1;
  right_o2_getCardId = _cardId1;
  right_o2_cardType = _cardType1;
}

void left(void) {

     int ret;

     if (left_o1 == left_o2){
       ret = 0;
     }
		 else if (left_o1_getCardSet > left_o2_getCardSet) {
		     ret =  1;
		 }
		 else if (left_o1_getCardSet < left_o2_getCardSet) {
		     ret =  -1;
		 }
		 else if (left_o1_getCardRarity < left_o2_getCardRarity) {
		     ret =  1;
		 }
		 else if (left_o1_getCardRarity > left_o2_getCardRarity) {
		     ret =  -1;
		 }
		 else if (left_o1_getCardId > left_o2_getCardId) {
		     ret =  1;
		 }
		 else if (left_o1_getCardId < left_o2_getCardId) {
		     ret =  -1;
		 } else {
       ret =  left_o1_cardType - left_o2_cardType;  //watch out for overflow!
     }
}

void right(void) {

     int ret;

     if (right_o1 == right_o2){
       ret = 0;
     }
		 else if (right_o1_getCardSet > right_o2_getCardSet) {
		     ret =  1;
		 }
		 else if (right_o1_getCardSet < right_o2_getCardSet) {
		     ret =  -1;
		 }
		 else if (right_o1_getCardRarity < right_o2_getCardRarity) {
		     ret =  1;
		 }
		 else if (right_o1_getCardRarity > right_o2_getCardRarity) {
		     ret =  -1;
		 }
		 else if (right_o1_getCardId > right_o2_getCardId) {
		     ret =  1;
		 }
		 else if (right_o1_getCardId < right_o2_getCardId) {
		     ret =  -1;
		 } else {
       ret =  right_o1_cardType - right_o2_cardType;  //watch out for overflow!
     }
}
