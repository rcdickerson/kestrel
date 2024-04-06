
function read(arr: int, index: int): int

function store(arr: int, index: int, value: int): int

function shift(arr: int, idx: int, amt: int): int

method Main(l_arr_in: int, l_len_in: int, l_val_in: int, r_arr_in: int, r_len_in: int, r_val_in: int)
  decreases *
 {
  assume((l_val_in > 0) && ((r_val_in > 0) && ((l_len_in >= 0) && ((r_len_in >= 0) && ((l_len_in == r_len_in) && (forall i: int :: (read(l_arr_in, i) == read(r_arr_in, i)) && (forall i: int, j: int, a: int, x: int :: ((!(i == j)) || (read(store(a, i, x), j) == x)) && forall i: int, j: int, a: int, x: int :: ((!(i != j)) || (read(store(a, i, x), j) == read(a, j))))))))));
  var l_arr: int := l_arr_in;
  var l_len: int := l_len_in;
  var l_val: int := l_val_in;
  var l_i: int := 0;
  while ((l_i < l_len) && (read(l_arr, l_i) < l_val))
    decreases *
    invariant l_val != 0
    invariant l_i >= 0
  {
    l_i := (l_i + 1);
  }
  l_arr := shift(l_arr, l_i, 1);
  l_len := (l_len + 1);
  l_arr := store(l_arr, l_i, l_val);
  while (l_i < l_len)
    decreases *
    invariant l_len != 0
    invariant l_val != 0
    invariant l_i >= 0
  {
    l_i := (l_i + 1);
  }
  var r_arr: int := r_arr_in;
  var r_len: int := r_len_in;
  var r_val: int := r_val_in;
  var r_j: int := 0;
  while ((r_j < r_len) && (read(r_arr, r_j) < r_val))
    decreases *
    invariant l_len <= l_i
    invariant l_len != 0
    invariant l_val != 0
    invariant r_val != 0
    invariant r_j >= 0
    invariant (l_len - (r_len - 1)) >= 0
    invariant l_len > r_j
  {
    r_j := (r_j + 1);
  }
  r_arr := shift(r_arr, r_j, 1);
  r_len := (r_len + 1);
  r_arr := store(r_arr, r_j, r_val);
  while (r_j < r_len)
    decreases *
    invariant l_len <= l_i
    invariant l_len == r_len
    invariant l_len <= r_len
    invariant l_len >= r_len
    invariant l_len != 0
    invariant l_val != 0
    invariant r_val != 0
    invariant r_j >= 0
  {
    r_j := (r_j + 1);
  }
  assert(l_i == r_j);
 }
