/* @KESTREL
 * pre: true;
 * left: ttt_search;
 * right: bst_search;
 * post: left.found == right.found;
 */

// 2-3 tree interface.
int ttt_lval(int tree);
int ttt_rval(int tree);
int ttt_left(int tree);
int ttt_center(int tree);
int ttt_right(int tree);
int ttt_null(int tree);

// BST interface.
int bst_val(int tree);
int bst_left(int tree);
int bst_right(int tree);
int bst_null(int tree);

void ttt_search(int tree_in, int val) {
  int found = 0;
  int t = tree_in;
  while (ttt_null(t) != 0) {
    if (ttt_lval(t) == val) {
      found = 1;
      break;
    } else if (val < ttt_lval(t)) {
      t = ttt_left(t);
    } else if (ttt_null(ttt_center(t)) == 0) {
      // 3-node is present - val > lval
      if (ttt_rval(t) == val) {
        found = 1;
        break;
      } else if(val < ttt_rval(t)) {
        t = ttt_center(t);
      } else {
        t = ttt_right(t);
      }
    } else {
      //right of 2-node
      t = ttt_right(t);
    }
  }
}

void bst_search(int tree_in, int val) {
  int found = 0;
  int t = tree_in;
  while (bst_null(t) != 0) {
    if (bst_val(t) == val) {
      found = 1;
      break;
    } else if(val < bst_val(t)) {
      t = bst_left(t);
    } else {
      t = bst_right(t);
    }
  }
}
