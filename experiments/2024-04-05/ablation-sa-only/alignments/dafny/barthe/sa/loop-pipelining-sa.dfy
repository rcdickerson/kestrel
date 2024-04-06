
function read(list_id: int, index: int): int

function store(list_id: int, index: int, value: int): int

method Main(l_a_in: int, l_b_in: int, l_c_in: int, l_size_in: int, r_a_in: int, r_b_in: int, r_c_in: int, r_size_in: int)
  decreases *
 {
  assume(forall i: int :: (read(l_a_in, i) == read(r_a_in, i)) && (forall i: int :: (read(l_b_in, i) == read(r_b_in, i)) && (forall i: int :: (read(l_c_in, i) == read(r_c_in, i)) && ((l_size_in == r_size_in) && ((2 <= l_size_in) && (forall i: int, j: int, a: int, x: int :: ((!(i == j)) || (read(store(a, i, x), j) == x)) && forall i: int, j: int, a: int, x: int :: ((!(i != j)) || (read(store(a, i, x), j) == read(a, j)))))))));
  var l_a: int := l_a_in;
  var l_b: int := l_b_in;
  var l_c: int := l_c_in;
  var l_size: int := l_size_in;
  var l_i: int := 0;
  var r_a: int := r_a_in;
  var r_b: int := r_b_in;
  var r_c: int := r_c_in;
  var r_size: int := r_size_in;
  var r_j: int := 0;
  r_a := store(r_a, 0, read(r_a, 0) + 1);
  r_b := store(r_b, 0, read(r_b, 0) + read(r_a, 0));
  r_a := store(r_a, 1, read(r_a, 1) + 1);
  if (l_i < l_size) {
    l_a := store(l_a, l_i, read(l_a, l_i) + 1);
    l_b := store(l_b, l_i, read(l_b, l_i) + read(l_a, l_i));
    l_c := store(l_c, l_i, read(l_c, l_i) + read(l_b, l_i));
    l_i := (l_i + 1);
  }
  if (l_i < l_size) {
    l_a := store(l_a, l_i, read(l_a, l_i) + 1);
    l_b := store(l_b, l_i, read(l_b, l_i) + read(l_a, l_i));
    l_c := store(l_c, l_i, read(l_c, l_i) + read(l_b, l_i));
    l_i := (l_i + 1);
  }
  while ((l_i < l_size) && (r_j < (r_size - 2)))
    decreases *
    invariant forall i: int :: (read(l_a, i) == read(r_a, i))
    invariant read(l_c, r_j + 1) == (read(r_c, r_j + 1) + read(l_b, r_j + 1))
    invariant forall i: int :: ((!(i != (r_j + 1))) || (read(l_b, i) == read(r_b, i)))
    invariant forall i: int :: ((!((i != r_j) && (i != (r_j + 1)))) || (read(l_c, i) == read(r_c, i)))
    invariant l_i == (r_j + 2)
    invariant read(l_c, r_j) == (read(r_c, r_j) + read(l_b, r_j))
    invariant read(l_b, r_j + 1) == (read(r_b, r_j + 1) + read(l_a, r_j + 1))
    invariant l_size == r_size
    invariant l_size <= r_size
    invariant l_size >= r_size
    invariant l_size != 0
    invariant l_i != 0
    invariant l_i >= 2
    invariant r_j >= 0
    invariant l_size > r_j
    invariant (l_i - (r_j - 2)) >= 0
  {
    l_a := store(l_a, l_i, read(l_a, l_i) + 1);
    l_b := store(l_b, l_i, read(l_b, l_i) + read(l_a, l_i));
    l_c := store(l_c, l_i, read(l_c, l_i) + read(l_b, l_i));
    l_i := (l_i + 1);
    r_a := store(r_a, r_j + 2, read(r_a, r_j + 2) + 1);
    r_b := store(r_b, r_j + 1, read(r_b, r_j + 1) + read(r_a, r_j + 1));
    r_c := store(r_c, r_j, read(r_c, r_j) + read(r_b, r_j));
    r_j := (r_j + 1);
  }
  if (l_i < l_size) {
    while (l_i < l_size)
      decreases *
      invariant forall i: int :: (read(l_a, i) == read(r_a, i))
      invariant read(l_c, r_j + 1) == (read(r_c, r_j + 1) + read(l_b, r_j + 1))
      invariant forall i: int :: ((!(i != (r_j + 1))) || (read(l_b, i) == read(r_b, i)))
      invariant forall i: int :: ((!((i != r_j) && (i != (r_j + 1)))) || (read(l_c, i) == read(r_c, i)))
      invariant l_i == (r_j + 2)
      invariant read(l_c, r_j) == (read(r_c, r_j) + read(l_b, r_j))
      invariant read(l_b, r_j + 1) == (read(r_b, r_j + 1) + read(l_a, r_j + 1))
    {
      l_a := store(l_a, l_i, read(l_a, l_i) + 1);
      l_b := store(l_b, l_i, read(l_b, l_i) + read(l_a, l_i));
      l_c := store(l_c, l_i, read(l_c, l_i) + read(l_b, l_i));
      l_i := (l_i + 1);
    }
  }
  if (r_j < (r_size - 2)) {
    while (r_j < (r_size - 2)) {
      r_a := store(r_a, r_j + 2, read(r_a, r_j + 2) + 1);
      r_b := store(r_b, r_j + 1, read(r_b, r_j + 1) + read(r_a, r_j + 1));
      r_c := store(r_c, r_j, read(r_c, r_j) + read(r_b, r_j));
      r_j := (r_j + 1);
    }
  }
  r_c := store(r_c, r_j, read(r_c, r_j) + read(r_b, r_j));
  r_b := store(r_b, r_j + 1, read(r_b, r_j + 1) + read(r_a, r_j + 1));
  r_c := store(r_c, r_j + 1, read(r_c, r_j + 1) + read(r_b, r_j + 1));
  assert(forall i: int :: (read(l_a, i) == read(r_a, i)) && (forall i: int :: (read(l_b, i) == read(r_b, i)) && forall i: int :: (read(l_c, i) == read(r_c, i))));
 }
