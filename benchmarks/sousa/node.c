/* @KESTREL
 * pre: left_o1_contains_id == right_o2_contains_id &&
        left_o1_get_id      == right_o2_get_id &&
        left_o1_contains_id == right_o2_contains_id &&
        left_o1_get_id      == right_o2_get_id;
 * left: left;
 * right: right;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://stackoverflow.com/questions/19325256/java-lang-illegalargumentexception-comparison-method-violates-its-general-contr
 *
 */

int left_o1_contains_id;
int left_o1_get_id;
int left_o2_contains_id;
int left_o2_get_id;

int right_o1_contains_id;
int right_o1_get_id;
int right_o2_contains_id;
int right_o2_get_id;

void _test_gen(int _contains_id1, int _contains_id2, int _get_id1, int _get_id2) {
  left_o1_contains_id = _contains_id1;
  left_o1_get_id = _get_id1;
  left_o2_contains_id = _contains_id2;
  left_o2_get_id = _contains_id2;
  right_o1_contains_id = _contains_id2;
  right_o1_get_id = _get_id2;
  right_o2_contains_id = _contains_id1;
  right_o2_get_id = _contains_id1;
}

void left(void) {
  int ret = -999;

  if(left_o1_contains_id && left_o2_contains_id) {
      int order1 = left_o1_get_id;
      int order2 = left_o2_get_id;

      if(order1 < order2)
        ret = -1;
      else if(order1 > order2)
        ret = 1;
      else
        ret = 0;
  }

  if (ret == -999) ret = left_o1_get_id - left_o2_get_id;
}

void right(void) {
  int ret = -999;

  if(right_o1_contains_id && right_o2_contains_id) {
      int order1 = right_o1_get_id;
      int order2 = right_o2_get_id;

      if(order1 < order2)
        ret = -1;
      else if(order1 > order2)
        ret = 1;
      else
        ret = 0;
  }

  if (ret == -999) ret = right_o1_get_id - right_o2_get_id;
}
