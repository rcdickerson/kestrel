
function bst_val(tree: int): int

function bst_left(tree: int): int

function bst_right(tree: int): int

function bst_null(tree: int): int

method Main(l_tree_in: int, l_val_in: int, r_tree_in: int, r_val_in: int)
  decreases *
 {
  assume((l_val_in <= r_val_in) && (l_tree_in == r_tree_in));
  var l_tree: int := l_tree_in;
  var l_val: int := l_val_in;
  var l_found: int := 0;
  var r_tree: int := r_tree_in;
  var r_val: int := r_val_in;
  var r_found: int := 0;
  while ((bst_null(bst_left(l_tree)) == 0) && (bst_null(bst_left(r_tree)) == 0))
    decreases *
    invariant l_tree == r_tree
    invariant l_tree <= r_tree
    invariant l_tree >= r_tree
    invariant l_found == 0
    invariant l_found <= 0
    invariant l_found >= 0
    invariant r_found == 0
    invariant r_found <= 0
    invariant r_found >= 0
  {
    l_tree := bst_left(l_tree);
    r_tree := bst_left(r_tree);
  }
  if (bst_null(bst_left(l_tree)) == 0) {
    while (bst_null(bst_left(l_tree)) == 0) {
      l_tree := bst_left(l_tree);
    }
  }
  if (bst_null(bst_left(r_tree)) == 0) {
    while (bst_null(bst_left(r_tree)) == 0) {
      r_tree := bst_left(r_tree);
    }
  }
  if (l_val < bst_val(l_tree)) {
    l_found := 1;
  }
  if (r_val < bst_val(r_tree)) {
    r_found := 1;
  }
  assert(r_found <= l_found);
 }
