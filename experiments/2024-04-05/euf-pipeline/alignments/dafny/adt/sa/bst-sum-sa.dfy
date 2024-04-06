
function bst_val(tree: int): int

function bst_left(tree: int): int

function bst_right(tree: int): int

method Main(l_tree_in: int, l_depth: int, r_tree_in: int, r_depth: int)
  decreases *
 {
  assume(forall t: int :: (bst_val(bst_left(t)) <= bst_val(bst_right(t))) && ((l_tree_in == r_tree_in) && (l_depth == r_depth)));
  var l_tree: int := l_tree_in;
  var l_sum: int := 0;
  var l_i: int := 0;
  var r_tree: int := r_tree_in;
  var r_sum: int := 0;
  var r_i: int := 0;
  while ((l_i < l_depth) && (r_i < r_depth))
    decreases *
    invariant l_tree == r_tree
    invariant l_tree <= r_tree
    invariant l_tree >= r_tree
    invariant l_sum <= r_sum
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_i >= 0
  {
    l_sum := (l_sum + bst_val(bst_left(l_tree)));
    l_tree := bst_left(l_tree);
    l_i := (l_i + 1);
    r_sum := (r_sum + bst_val(bst_right(r_tree)));
    r_tree := bst_left(r_tree);
    r_i := (r_i + 1);
  }
  if (l_i < l_depth) {
    while (l_i < l_depth) {
      l_sum := (l_sum + bst_val(bst_left(l_tree)));
      l_tree := bst_left(l_tree);
      l_i := (l_i + 1);
    }
  }
  if (r_i < r_depth) {
    while (r_i < r_depth) {
      r_sum := (r_sum + bst_val(bst_right(r_tree)));
      r_tree := bst_left(r_tree);
      r_i := (r_i + 1);
    }
  }
  assert(l_sum <= r_sum);
 }
