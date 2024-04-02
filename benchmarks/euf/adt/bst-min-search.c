/* @KESTREL
 * pre: left.val_in <= right.val_in
     && left.tree_in == right.tree_in;
 * left: search;
 * right: search;
 * post: right.found <= left.found;
 */

// BST interface.
int bst_val(int tree);
int bst_left(int tree);
int bst_right(int tree);
int bst_null(int tree);

void _test_gen(int tree, int val1, int val2) {
  if (val1 <= val2) {
    _main(tree, val1, tree, val2);
  } else {
    _main(tree, val2, tree, val1);
  }
}

int _bst_null(int tree) {
  if (tree % 5 == 0) {
    return 1;
  } else {
    return 0;
  }
}

void search(int tree_in, int val_in) {
  int tree = tree_in;
  int val = val_in;
  int found = 0;
  while(bst_null(bst_left(tree)) == 0) {
    _invariant("left.val <= right.val");
    tree = bst_left(tree);
  }
  if(val < bst_val(tree)) {
    found = 1;
  }
}
