
function read(arr: int, index: int): int

function store(arr: int, index: int, value: int): int

function f(anon: int): int

method Main(l_a_in: int, l_n_in: int, l_m_in: int, r_a_in: int, r_n_in: int, r_m_in: int)
  decreases *
 {
  assume((l_a_in == r_a_in) && ((l_n_in == r_n_in) && (l_m_in == r_m_in)));
  var l_a: int := l_a_in;
  var l_n: int := l_n_in;
  var l_m: int := l_m_in;
  var l_x: int := 0;
  while (l_x < (l_n * l_m))
    decreases *
    invariant l_x >= 0
  {
    l_a := store(l_a, l_x, f(l_x));
    l_x := (l_x + 1);
  }
  var r_a: int := r_a_in;
  var r_n: int := r_n_in;
  var r_m: int := r_m_in;
  var r_i: int := 0;
  while (r_i < r_n)
    decreases *
    invariant l_n == r_n
    invariant l_n <= r_n
    invariant l_n >= r_n
    invariant l_m == r_m
    invariant l_m <= r_m
    invariant l_m >= r_m
    invariant l_x >= 0
    invariant r_i >= 0
  {
    var r_j: int := 0;
    while (r_j < r_m)
      decreases *
      invariant l_n == r_n
      invariant l_n <= r_n
      invariant l_n >= r_n
      invariant l_m == r_m
      invariant l_m <= r_m
      invariant l_m >= r_m
      invariant l_n != 0
      invariant l_n >= 1
      invariant r_i >= 0
      invariant r_j >= 0
      invariant l_n > r_i
      invariant l_m <= l_x
    {
      r_a := store(r_a, r_i, store(read(r_a, r_i), r_j, f((r_i * r_n) + r_j)));
      r_j := (r_j + 1);
    }
    r_i := (r_i + 1);
  }
  assert(forall i: int, j: int :: (read(l_a, (i * l_n) + j) == read(read(r_a, i), j)));
 }
