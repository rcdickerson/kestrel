
function list_val(list: int): int

function list_next(list: int): int

function list_null(list: int): int

function read(list_id: int, index: int): int

function store(list_id: int, index: int, value: int): int

function r_advance(l1: int, l2: int, n: int): int

method Main(l_list_in: int, l_length: int, r_arr_in: int, r_length: int)
  decreases *
 {
  assume((l_length == r_length) && (forall list: int :: (r_advance(list, list, 0) == 1) && (forall l1: int, l2: int :: ((!(l1 != l2)) || (r_advance(l1, l2, 0) == 0)) && (forall l1: int, l2: int, l2next: int, n: int, m: int :: ((!((l2next == list_next(l2)) && ((r_advance(l1, l2, n) == 1) && (m == (n + 1))))) || (r_advance(l1, l2next, m) == 1)) && forall list: int, n: int :: ((!(r_advance(l_list_in, list, n) == 1)) || (list_val(list) == read(r_arr_in, n)))))));
  var l_sum: int := 0;
  var l_list: int := l_list_in;
  var l_i: int := 0;
  var r_sum: int := 0;
  var r_i: int := 0;
  while ((l_i < l_length) && (r_i < r_length))
    decreases *
    invariant l_sum == r_sum
    invariant r_advance(l_list_in, l_list, l_i) == 1
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_i >= 0
  {
    l_sum := (l_sum + list_val(l_list));
    l_list := list_next(l_list);
    l_i := (l_i + 1);
    r_sum := (r_sum + read(r_arr_in, r_i));
    r_i := (r_i + 1);
  }
  if (l_i < l_length) {
    while (l_i < l_length)
      decreases *
      invariant l_sum == r_sum
      invariant r_advance(l_list_in, l_list, l_i) == 1
    {
      l_sum := (l_sum + list_val(l_list));
      l_list := list_next(l_list);
      l_i := (l_i + 1);
    }
  }
  if (r_i < r_length) {
    while (r_i < r_length) {
      r_sum := (r_sum + read(r_arr_in, r_i));
      r_i := (r_i + 1);
    }
  }
  assert(l_sum == r_sum);
 }
