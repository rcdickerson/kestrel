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

int right_o1_contains_id;
int right_o1_get_id;
int right_o2_contains_id;
int right_o2_get_id;

void _test_gen(int contains_id1, int contains_id2, int get_id1, int get_id2) {
  _main(contains_id1, get_id1,
        contains_id2, get_id2,
        contains_id2, get_id2,
        contains_id1, get_id1);
}

void compare(int o1_contains_id,
             int o1_get_id,
             int o2_contains_id,
             int o2_get_id) {
  int ret = -999;

  if(o1_contains_id && o2_contains_id) {
      int order1 = o1_get_id;
      int order2 = o2_get_id;

      if(order1 < order2)
        ret = -1;
      else if(order1 > order2)
        ret = 1;
      else
        ret = 0;
  }

  if (ret == -999) ret = o1_get_id - o2_get_id;
}
