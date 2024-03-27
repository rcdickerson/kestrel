/* @KESTREL
 * pre: (forall t: int :: bst_val(bst_left(t)) <= bst_val(bst_right(t)))
     && left.tree_in == right.tree_in
     && left.depth == right.depth;
 * left: left_sum;
 * right: right_sum;
 * post: left.sum <= right.sum;
 */

int bst_val(int tree);
int bst_left(int tree);
int bst_right(int tree);

void _test_gen(int tree, int depth) {
  if (depth < 0) { depth = depth * -1; }
  depth = depth % 100;
  _main(tree, depth, tree, depth);
}

void left_sum(int tree_in, int depth) {
  int tree = tree_in;
  int sum = 0;
  int i = 0;
  while (i < depth) {
    // invariant l_sum <= r_sum
    sum = sum + bst_val(bst_left(tree));
    tree = bst_left(tree);
    i = i + 1;
  }
}

void right_sum(int tree_in, int depth) {
  int tree = tree_in;
  int sum = 0;
  int i = 0;
  while (i < depth) {
    // invariant l_sum <= r_sum
    sum = sum + bst_val(bst_right(tree));
    tree = bst_left(tree);
    i = i + 1;
  }
}
