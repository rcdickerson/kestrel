
function list_val(list: int): int

function list_next(list: int): int

function list_cons(head: int, list: int): int

function list_null(list: int): int

method Main(l_lst_in: int, l_target: int, l_h_secret_in: int, r_lst_in: int, r_target: int, r_h_secret_in: int)
  decreases *
 {
  assume((l_lst_in == r_lst_in) && ((l_target == r_target) && forall head: int, lst: int :: (list_next(list_cons(head, lst)) == lst)));
  var l_lst: int := l_lst_in;
  var l_h_secret: int := l_h_secret_in;
  l_lst := list_cons(l_h_secret, l_lst);
  l_lst := list_next(l_lst);
  var l_found_at: int := -1;
  var l_i: int := 0;
  var r_lst: int := r_lst_in;
  var r_h_secret: int := r_h_secret_in;
  r_lst := list_cons(r_h_secret, r_lst);
  r_lst := list_next(r_lst);
  var r_found_at: int := -1;
  var r_i: int := 0;
  while ((list_null(l_lst) == 0) && (list_null(r_lst) == 0))
    decreases *
    invariant l_target == r_target
    invariant l_found_at == r_found_at
    invariant l_i == r_i
    invariant l_lst == r_lst
    invariant l_found_at >= -1
    invariant r_found_at >= -1
  {
    l_i := (l_i + 1);
    l_lst := list_next(l_lst);
    r_i := (r_i + 1);
    r_lst := list_next(r_lst);
    if ((list_null(l_lst) == 0) && (list_val(l_lst) == l_target)) {
      l_found_at := l_i;
    }
    if ((list_null(r_lst) == 0) && (list_val(r_lst) == r_target)) {
      r_found_at := r_i;
    }
  }
  while (list_null(l_lst) == 0)
    decreases *
    invariant l_target == r_target
    invariant l_found_at == r_found_at
    invariant l_i == r_i
    invariant l_lst == r_lst
    invariant l_found_at >= -1
    invariant l_i >= 0
    invariant r_found_at >= -1
    invariant r_i >= 0
  {
    l_i := (l_i + 1);
    l_lst := list_next(l_lst);
    if ((list_null(l_lst) == 0) && (list_val(l_lst) == l_target)) {
      l_found_at := l_i;
    }
  }
  while (list_null(r_lst) == 0)
    decreases *
    invariant l_i == r_i
    invariant l_target == r_target
    invariant l_found_at == r_found_at
    invariant l_lst == r_lst
    invariant l_found_at >= -1
    invariant r_found_at >= -1
    invariant r_i >= 0
  {
    r_i := (r_i + 1);
    r_lst := list_next(r_lst);
    if ((list_null(r_lst) == 0) && (list_val(r_lst) == r_target)) {
      r_found_at := r_i;
    }
  }
  assert(l_found_at == r_found_at);
 }
