
function read(list_id: int, index: int): int

function store(list_id: int, index: int, value: int): int

method Main(l_a_in: int, l_b_in: int, l_size_in: int, r_a_in: int, r_b_in: int, r_size_in: int)
  decreases *
 {
  assume((l_a_in == r_a_in) && ((l_b_in == r_b_in) && ((l_size_in == r_size_in) && ((1 <= l_size_in) && (forall i: int, j: int, a: int, x: int :: ((!(i == j)) || (read(store(a, i, x), j) == x)) && forall i: int, j: int, a: int, x: int :: ((!(i != j)) || (read(store(a, i, x), j) == read(a, j))))))));
  var l_a: int := l_a_in;
  var l_b: int := l_b_in;
  var l_size: int := l_size_in;
  var l_i: int := 1;
  var l_d: int := (l_a + l_b) + 1;
  var r_a: int := r_a_in;
  var r_b: int := r_b_in;
  var r_size: int := r_size_in;
  var r_j: int := 1;
  var r_d: int := (r_a + r_b) + 1;
  r_d := store(r_d, 1, read(r_b, 0));
  while ((l_i <= l_size) && (r_j <= (r_size - 1)))
    decreases *
    invariant l_a == r_a
    invariant l_a <= r_a
    invariant l_a >= r_a
    invariant l_b == r_b
    invariant l_b <= r_b
    invariant l_b >= r_b
    invariant l_size == r_size
    invariant l_size <= r_size
    invariant l_size >= r_size
    invariant l_i == r_j
    invariant l_i <= r_j
    invariant l_i >= r_j
    invariant l_size != 0
    invariant l_i != 0
    invariant l_i >= 1
  {
    l_b := store(l_b, l_i, read(l_a, l_i));
    l_d := store(l_d, l_i, read(l_b, l_i - 1));
    l_i := (l_i + 1);
    r_b := store(r_b, r_j, read(r_a, r_j));
    r_d := store(r_d, r_j + 1, read(r_b, r_j));
    r_j := (r_j + 1);
  }
  while (l_i <= l_size)
    decreases *
    invariant l_a == r_a
    invariant l_a <= r_a
    invariant l_a >= r_a
    invariant l_size <= l_i
    invariant l_size == r_size
    invariant l_size <= r_size
    invariant l_size >= r_size
    invariant l_size <= r_j
    invariant l_size != 0
  {
    l_b := store(l_b, l_i, read(l_a, l_i));
    l_d := store(l_d, l_i, read(l_b, l_i - 1));
    l_i := (l_i + 1);
  }
  if (r_j <= (r_size - 1)) {
    while (r_j <= (r_size - 1)) {
      r_b := store(r_b, r_j, read(r_a, r_j));
      r_d := store(r_d, r_j + 1, read(r_b, r_j));
      r_j := (r_j + 1);
    }
  }
  r_b := store(r_b, r_size, read(r_a, r_size));
  assert(l_d == r_d);
 }
