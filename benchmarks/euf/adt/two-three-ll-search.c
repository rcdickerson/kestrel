/* @KESTREL
 * pre: true;
 * left: tree_search;
 * right: list_search;
 * post: left.found == right.found;
 */

// 2-3 tree interface.
int tree_lval(int tree);
int tree_rval(int tree);
int tree_left(int tree);
int tree_center(int tree);
int tree_right(int tree);
int tree_null(int tree);

// Linked list interface.
int list_val(int list);
int list_next(int list);
int list_null(int list);

void tree_search(int tree_in, int val) {
  int found = 0;
  int t = tree_in;
  while(tree_null(t) != 0) {
    if(tree_lval(t) == val) {
      found = 1;
      break;
    } else if(val < tree_lval(t)) {
      t = tree_left(t);
    } else if(tree_null(tree_center(t)) == 0) {
      // 3-node is present - val > lval
      if(tree_rval(t) == val) {
        found = 1;
        break;
      } else if(val < tree_rval(t)) {
        t = tree_center(t);
      } else {
        t = tree_right(t);
      }
    } else {
      // right of 2-node
      t = tree_right(t);
    }
  }
}

void list_search(int list_in, int val) {
  int found = 0;
  int l = list_in;
  while(list_null(l) == 0) {
    if(list_val(l) == val) {
      found = 1;
      break;
    }
    l = list_next(l);
  }
}
