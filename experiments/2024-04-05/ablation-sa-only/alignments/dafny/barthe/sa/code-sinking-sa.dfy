
function read(list_id: int, index: int): int

function store(list_id: int, index: int, value: int): int

method Main(l_a_in: int, l_size: int, r_a_in: int, r_size: int)
  decreases *
 {
  assume(forall i: int :: (read(l_a_in, i) == read(r_a_in, i)) && ((l_size == r_size) && ((l_size > 0) && (forall i: int, j: int, a: int, x: int :: ((!(i == j)) || (read(store(a, i, x), j) == x)) && forall i: int, j: int, a: int, x: int :: ((!(i != j)) || (read(store(a, i, x), j) == read(a, j)))))));
  var r_a: int := r_a_in;
  var r_j: int := 0;
  var r_max: int := 0;
  var r_maxi: int := 0;
  var l_a: int := l_a_in;
  var l_max: int := read(l_a, 0);
  var l_maxi: int := 0;
  var l_i: int := 0;
  if (l_i <= l_size) {
    if (l_max < read(l_a, l_i)) {
      l_max := read(l_a, l_i);
      l_maxi := l_i;
    }
    l_i := (l_i + 1);
  }
  while ((l_i <= l_size) && (r_j <= r_size))
    decreases *
    invariant (!(r_j == (r_size + 1))) || (read(l_a, l_size) == read(r_a, r_maxi))
    invariant (!(r_j == (r_size + 1))) || forall i: int :: ((!((i != r_maxi) && (i != r_size))) || (read(l_a, i) == read(r_a, i)))
    invariant 0 <= l_maxi
    invariant l_max == read(l_a, l_maxi)
    invariant (0 <= r_maxi) && (r_maxi <= r_j)
    invariant (0 <= r_j) && (r_j <= (r_size + 1))
    invariant (0 <= l_maxi) && (l_maxi <= l_i)
    invariant (0 <= l_i) && (l_i <= (l_size + 1))
    invariant 0 <= r_maxi
    invariant (!(r_j <= r_size)) || forall i: int :: (read(l_a, i) == read(r_a, i))
    invariant r_j >= 0
    invariant r_maxi >= 0
    invariant l_i != 0
    invariant l_i >= 1
    invariant r_j >= r_maxi
    invariant (r_j - (l_i + 1)) <= 0
  {
    if (r_j == 0) {
      r_max := read(r_a, 0);
      r_maxi := 0;
    }
    if (r_max < read(r_a, r_j)) {
      r_max := read(r_a, r_j);
      r_maxi := r_j;
    }
    if (l_max < read(l_a, l_i)) {
      l_max := read(l_a, l_i);
      l_maxi := l_i;
    }
    if (r_j == r_size) {
      var r_t: int := read(r_a, r_size);
      r_a := store(r_a, r_size, r_max);
      r_a := store(r_a, r_maxi, r_t);
    }
    l_i := (l_i + 1);
    r_j := (r_j + 1);
  }
  if (l_i <= l_size) {
    while (l_i <= l_size)
      decreases *
      invariant (!(r_j == (r_size + 1))) || (read(l_a, l_size) == read(r_a, r_maxi))
      invariant (!(r_j == (r_size + 1))) || forall i: int :: ((!((i != r_maxi) && (i != r_size))) || (read(l_a, i) == read(r_a, i)))
      invariant 0 <= l_maxi
      invariant l_max == read(l_a, l_maxi)
      invariant (0 <= r_maxi) && (r_maxi <= r_j)
      invariant (0 <= r_j) && (r_j <= (r_size + 1))
      invariant (0 <= l_maxi) && (l_maxi <= l_i)
      invariant (0 <= l_i) && (l_i <= (l_size + 1))
      invariant (0 < r_j) && ((!(r_j <= r_size)) || (r_max == read(r_a, r_maxi)))
      invariant 0 <= r_maxi
      invariant (!(r_j <= r_size)) || forall i: int :: (read(l_a, i) == read(r_a, i))
    {
      if (l_max < read(l_a, l_i)) {
        l_max := read(l_a, l_i);
        l_maxi := l_i;
      }
      l_i := (l_i + 1);
    }
  }
  while (r_j <= r_size)
    decreases *
    invariant l_i != 0
    invariant (r_j - (r_maxi - 1)) >= 0
    invariant (r_j - (l_i + 1)) <= 0
    invariant (r_maxi - (l_i + 2)) <= 0
  {
    if (r_j == 0) {
      r_max := read(r_a, 0);
      r_maxi := 0;
    }
    if (r_max < read(r_a, r_j)) {
      r_max := read(r_a, r_j);
      r_maxi := r_j;
    }
    if (r_j == r_size) {
      var r_t: int := read(r_a, r_size);
      r_a := store(r_a, r_size, r_max);
      r_a := store(r_a, r_maxi, r_t);
    }
    r_j := (r_j + 1);
  }
  var l_t: int := read(l_a, l_size);
  l_a := store(l_a, l_size, l_max);
  l_a := store(l_a, l_maxi, l_t);
  assert(forall i: int :: (read(l_a, i) == read(r_a, i)));
 }
