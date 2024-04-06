
function read(list_id: int, index: int): int

function store(list_id: int, index: int, value: int): int

method Main(l_a_in: int, l_b_in: int, l_c_in: int, l_k_in: int, l_x_in: int, l_size: int, r_a_in: int, r_b_in: int, r_c_in: int, r_k_in: int, r_x_in: int, r_size: int)
  decreases *
 {
  assume((l_k_in == r_k_in) && ((l_x_in == r_x_in) && ((l_a_in == r_a_in) && ((l_b_in == r_b_in) && ((l_c_in == r_c_in) && ((l_size == r_size) && (forall i: int, j: int, a: int, x: int :: ((!(i == j)) || (read(store(a, i, x), j) == x)) && forall i: int, j: int, a: int, x: int :: ((!(i != j)) || (read(store(a, i, x), j) == read(a, j))))))))));
  var l_a: int := l_a_in;
  var l_b: int := l_b_in;
  var l_c: int := l_c_in;
  var l_k: int := l_k_in;
  var l_x: int := l_x_in;
  var l_i: int := 0;
  var r_a: int := r_a_in;
  var r_b: int := r_b_in;
  var r_c: int := r_c_in;
  var r_k: int := r_k_in;
  var r_x: int := r_x_in;
  if (r_x < 7) {
    var r_j: int := 0;
    while ((l_i < l_size) && (r_j < r_size))
      decreases *
      invariant forall i: int :: (read(l_a, i) == read(r_a, i))
      invariant forall i: int :: (read(l_b, i) == read(r_b, i))
      invariant forall i: int :: (read(l_c, i) == read(r_c, i))
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_b == r_b
      invariant l_b <= r_b
      invariant l_b >= r_b
      invariant l_c == r_c
      invariant l_c <= r_c
      invariant l_c >= r_c
      invariant l_k == r_k
      invariant l_k <= r_k
      invariant l_k >= r_k
      invariant l_x == r_x
      invariant l_x <= r_x
      invariant l_x >= r_x
      invariant l_i == r_j
      invariant l_i <= r_j
      invariant l_i >= r_j
      invariant l_i >= 0
    {
      l_a := store(l_a, l_i, read(l_a, l_i) + l_k);
      if (l_x < 7) {
        l_b := store(l_b, l_i, read(l_a, l_i) * read(l_c, l_i));
      } else {
        l_b := store(l_b, l_i, read(l_a, l_i - 1) * read(l_b, l_i - 1));
      }
      l_i := (l_i + 1);
      r_a := store(r_a, r_j, read(r_a, r_j) + r_k);
      r_b := store(r_b, r_j, read(r_a, r_j) * read(r_c, r_j));
      r_j := (r_j + 1);
    }
    if (l_i < l_size) {
      while (l_i < l_size)
        decreases *
        invariant forall i: int :: (read(l_a, i) == read(r_a, i))
        invariant forall i: int :: (read(l_b, i) == read(r_b, i))
        invariant forall i: int :: (read(l_c, i) == read(r_c, i))
      {
        l_a := store(l_a, l_i, read(l_a, l_i) + l_k);
        if (l_x < 7) {
          l_b := store(l_b, l_i, read(l_a, l_i) * read(l_c, l_i));
        } else {
          l_b := store(l_b, l_i, read(l_a, l_i - 1) * read(l_b, l_i - 1));
        }
        l_i := (l_i + 1);
      }
    }
    if (r_j < r_size) {
      while (r_j < r_size) {
        r_a := store(r_a, r_j, read(r_a, r_j) + r_k);
        r_b := store(r_b, r_j, read(r_a, r_j) * read(r_c, r_j));
        r_j := (r_j + 1);
      }
    }
  } else {
    var r_j: int := 0;
    while ((l_i < l_size) && (r_j < r_size))
      decreases *
      invariant forall i: int :: (read(l_c, i) == read(r_c, i))
      invariant forall i: int :: (read(l_b, i) == read(r_b, i))
      invariant forall i: int :: (read(l_a, i) == read(r_a, i))
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_b == r_b
      invariant l_b <= r_b
      invariant l_b >= r_b
      invariant l_c == r_c
      invariant l_c <= r_c
      invariant l_c >= r_c
      invariant l_k == r_k
      invariant l_k <= r_k
      invariant l_k >= r_k
      invariant l_x == r_x
      invariant l_x <= r_x
      invariant l_x >= r_x
      invariant l_i == r_j
      invariant l_i <= r_j
      invariant l_i >= r_j
      invariant l_x != 0
      invariant l_i >= 0
    {
      l_a := store(l_a, l_i, read(l_a, l_i) + l_k);
      if (l_x < 7) {
        l_b := store(l_b, l_i, read(l_a, l_i) * read(l_c, l_i));
      } else {
        l_b := store(l_b, l_i, read(l_a, l_i - 1) * read(l_b, l_i - 1));
      }
      l_i := (l_i + 1);
      r_a := store(r_a, r_j, read(r_a, r_j) + r_k);
      r_b := store(r_b, r_j, read(r_a, r_j - 1) * read(r_b, r_j - 1));
      r_j := (r_j + 1);
    }
    if (l_i < l_size) {
      while (l_i < l_size)
        decreases *
        invariant forall i: int :: (read(l_c, i) == read(r_c, i))
        invariant forall i: int :: (read(l_b, i) == read(r_b, i))
        invariant forall i: int :: (read(l_a, i) == read(r_a, i))
      {
        l_a := store(l_a, l_i, read(l_a, l_i) + l_k);
        if (l_x < 7) {
          l_b := store(l_b, l_i, read(l_a, l_i) * read(l_c, l_i));
        } else {
          l_b := store(l_b, l_i, read(l_a, l_i - 1) * read(l_b, l_i - 1));
        }
        l_i := (l_i + 1);
      }
    }
    if (r_j < r_size) {
      while (r_j < r_size) {
        r_a := store(r_a, r_j, read(r_a, r_j) + r_k);
        r_b := store(r_b, r_j, read(r_a, r_j - 1) * read(r_b, r_j - 1));
        r_j := (r_j + 1);
      }
    }
  }
  assert(forall i: int :: (read(l_a, i) == read(r_a, i)) && (forall i: int :: (read(l_b, i) == read(r_b, i)) && forall i: int :: (read(l_c, i) == read(r_c, i))));
 }
