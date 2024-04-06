
function read(list_id: int, index: int): int

function store(list_id: int, index: int, value: int): int

method Main(l_a_in: int, l_M_in: int, l_N_in: int, l_L_in: int, r_a_in: int, r_M_in: int, r_N_in: int, r_L_in: int)
  decreases *
 {
  assume((l_a_in == r_a_in) && ((l_M_in == r_M_in) && ((l_N_in == r_N_in) && ((l_L_in == r_L_in) && (forall i: int, j: int, a: int, x: int :: ((!(i == j)) || (read(store(a, i, x), j) == x)) && forall i: int, j: int, a: int, x: int :: ((!(i != j)) || (read(store(a, i, x), j) == read(a, j))))))));
  var l_a: int := l_a_in;
  var l_M: int := l_M_in;
  var l_N: int := l_N_in;
  var l_L: int := l_L_in;
  var l_s: int := 0;
  var l_i: int := 0;
  var r_a: int := r_a_in;
  var r_M: int := r_M_in;
  var r_N: int := r_N_in;
  var r_L: int := r_L_in;
  var r_s: int := 0;
  var r_b: int := 1;
  r_s := store(r_s, 0, 0);
  var r_k: int := 0;
  while ((l_i < (l_N - l_M)) && (r_k <= (r_M - 1)))
    decreases *
    invariant l_a == r_a
    invariant l_a <= r_a
    invariant l_a >= r_a
    invariant l_M == r_M
    invariant l_M <= r_M
    invariant l_M >= r_M
    invariant l_N == r_N
    invariant l_N <= r_N
    invariant l_N >= r_N
    invariant l_L == r_L
    invariant l_L <= r_L
    invariant l_L >= r_L
  {
    l_s := store(l_s, l_i, 0);
    var l_k: int := 0;
    r_b := store(r_b, r_k, 0);
    var r_l: int := 0;
    while ((l_k <= (l_M - 1)) && (r_l <= (r_L - 1)))
      decreases *
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_M == r_M
      invariant l_M <= r_M
      invariant l_M >= r_M
      invariant l_N == r_N
      invariant l_N <= r_N
      invariant l_N >= r_N
      invariant l_L == r_L
      invariant l_L <= r_L
      invariant l_L >= r_L
      invariant l_k == r_l
      invariant l_k <= r_l
      invariant l_k >= r_l
      invariant l_M != 0
      invariant l_N != 0
      invariant l_i >= 0
      invariant l_k >= 0
      invariant l_M < l_N
      invariant l_N > l_i
      invariant l_N > l_k
    {
      var l_l: int := 0;
      while (l_l <= (l_L - 1))
        decreases *
        invariant l_a == r_a
        invariant l_a <= r_a
        invariant l_a >= r_a
        invariant l_M == r_M
        invariant l_M <= r_M
        invariant l_M >= r_M
        invariant l_N == r_N
        invariant l_N <= r_N
        invariant l_N >= r_N
        invariant l_L == r_L
        invariant l_L <= r_L
        invariant l_L >= r_L
        invariant l_k == r_l
        invariant l_k <= r_l
        invariant l_k >= r_l
        invariant l_M != 0
        invariant l_N != 0
        invariant l_L != 0
        invariant l_i >= 0
        invariant l_k >= 0
        invariant l_l >= 0
        invariant l_M < l_N
        invariant l_M > l_k
        invariant l_N > l_i
        invariant l_N > l_k
        invariant l_L > l_k
      {
        l_s := store(l_s, l_i, read(l_s, l_i) + read(read(l_a, l_i + l_k), l_l));
        l_l := (l_l + 1);
      }
      l_k := (l_k + 1);
      r_b := store(r_b, r_k, read(r_b, r_k) + read(read(r_a, r_k), r_l));
      r_l := (r_l + 1);
    }
    while (l_k <= (l_M - 1))
      decreases *
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_M == r_M
      invariant l_M <= r_M
      invariant l_M >= r_M
      invariant l_N == r_N
      invariant l_N <= r_N
      invariant l_N >= r_N
      invariant l_L == r_L
      invariant l_L <= r_L
      invariant l_L >= r_L
      invariant l_i >= 0
      invariant l_N > l_k
    {
      var l_l: int := 0;
      while (l_l <= (l_L - 1))
        decreases *
        invariant l_a == r_a
        invariant l_a <= r_a
        invariant l_a >= r_a
        invariant l_M == r_M
        invariant l_M <= r_M
        invariant l_M >= r_M
        invariant l_N == r_N
        invariant l_N <= r_N
        invariant l_N >= r_N
        invariant l_L == r_L
        invariant l_L <= r_L
        invariant l_L >= r_L
        invariant l_i >= 0
        invariant l_l >= 0
        invariant l_M > l_k
        invariant l_N > l_k
      {
        l_s := store(l_s, l_i, read(l_s, l_i) + read(read(l_a, l_i + l_k), l_l));
        l_l := (l_l + 1);
      }
      l_k := (l_k + 1);
    }
    while (r_l <= (r_L - 1))
      decreases *
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_M == r_M
      invariant l_M <= r_M
      invariant l_M >= r_M
      invariant l_M <= l_k
      invariant l_N == r_N
      invariant l_N <= r_N
      invariant l_N >= r_N
      invariant l_L == r_L
      invariant l_L <= r_L
      invariant l_L >= r_L
      invariant l_M != 0
      invariant l_N != 0
      invariant l_i >= 0
      invariant l_M < l_N
      invariant l_N > l_i
    {
      r_b := store(r_b, r_k, read(r_b, r_k) + read(read(r_a, r_k), r_l));
      r_l := (r_l + 1);
    }
    l_i := (l_i + 1);
    r_s := store(r_s, 0, read(r_s, 0) + read(r_b, r_k));
    r_k := (r_k + 1);
  }
  while (l_i < (l_N - l_M))
    decreases *
    invariant l_a == r_a
    invariant l_a <= r_a
    invariant l_a >= r_a
    invariant l_M == r_M
    invariant l_M <= r_M
    invariant l_M >= r_M
    invariant l_N == r_N
    invariant l_N <= r_N
    invariant l_N >= r_N
    invariant l_L == r_L
    invariant l_L <= r_L
    invariant l_L >= r_L
    invariant l_i >= 0
  {
    l_s := store(l_s, l_i, 0);
    var l_k: int := 0;
    while (l_k <= (l_M - 1))
      decreases *
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_M == r_M
      invariant l_M <= r_M
      invariant l_M >= r_M
      invariant l_N == r_N
      invariant l_N <= r_N
      invariant l_N >= r_N
      invariant l_L == r_L
      invariant l_L <= r_L
      invariant l_L >= r_L
      invariant l_k >= 0
    {
      var l_l: int := 0;
      while (l_l <= (l_L - 1))
        decreases *
        invariant l_a == r_a
        invariant l_a <= r_a
        invariant l_a >= r_a
        invariant l_M == r_M
        invariant l_M <= r_M
        invariant l_M >= r_M
        invariant l_N == r_N
        invariant l_N <= r_N
        invariant l_N >= r_N
        invariant l_L == r_L
        invariant l_L <= r_L
        invariant l_L >= r_L
        invariant l_M >= 1
        invariant l_k >= 0
        invariant l_l >= 0
        invariant l_N > l_i
      {
        l_s := store(l_s, l_i, read(l_s, l_i) + read(read(l_a, l_i + l_k), l_l));
        l_l := (l_l + 1);
      }
      l_k := (l_k + 1);
    }
    l_i := (l_i + 1);
  }
  while (r_k <= (r_M - 1))
    decreases *
    invariant l_a == r_a
    invariant l_a <= r_a
    invariant l_a >= r_a
    invariant l_M == r_M
    invariant l_M <= r_M
    invariant l_M >= r_M
    invariant l_N == r_N
    invariant l_N <= r_N
    invariant l_N >= r_N
    invariant l_L == r_L
    invariant l_L <= r_L
    invariant l_L >= r_L
    invariant r_k >= 0
  {
    r_b := store(r_b, r_k, 0);
    var r_l: int := 0;
    while (r_l <= (r_L - 1))
      decreases *
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_M == r_M
      invariant l_M <= r_M
      invariant l_M >= r_M
      invariant l_N == r_N
      invariant l_N <= r_N
      invariant l_N >= r_N
      invariant l_L == r_L
      invariant l_L <= r_L
      invariant l_L >= r_L
      invariant l_M != 0
      invariant l_M >= 1
      invariant r_k >= 0
      invariant r_l >= 0
      invariant l_M > r_k
    {
      r_b := store(r_b, r_k, read(r_b, r_k) + read(read(r_a, r_k), r_l));
      r_l := (r_l + 1);
    }
    r_s := store(r_s, 0, read(r_s, 0) + read(r_b, r_k));
    r_k := (r_k + 1);
  }
  var r_i: int := 1;
  while (r_i <= (r_N - r_M))
    decreases *
    invariant l_a == r_a
    invariant l_a <= r_a
    invariant l_a >= r_a
    invariant l_M == r_M
    invariant l_M <= r_M
    invariant l_M >= r_M
    invariant l_M <= r_k
    invariant l_N == r_N
    invariant l_N <= r_N
    invariant l_N >= r_N
    invariant l_L == r_L
    invariant l_L <= r_L
    invariant l_L >= r_L
    invariant r_i != 0
    invariant r_i >= 1
  {
    r_b := store(r_b, (r_i + r_M) - 1, 0);
    var r_l: int := 0;
    while (r_l <= (r_L - 1))
      decreases *
      invariant l_a == r_a
      invariant l_a <= r_a
      invariant l_a >= r_a
      invariant l_M == r_M
      invariant l_M <= r_M
      invariant l_M >= r_M
      invariant l_M <= r_k
      invariant l_N == r_N
      invariant l_N <= r_N
      invariant l_N >= r_N
      invariant l_L == r_L
      invariant l_L <= r_L
      invariant l_L >= r_L
      invariant l_i != 0
      invariant r_i != 0
      invariant r_i >= 1
      invariant r_l >= 0
      invariant l_M < l_N
      invariant l_i >= r_i
    {
      r_b := store(r_b, (r_i + r_M) - 1, read(r_b, (r_i + r_M) - 1) + read(read(r_a, (r_i + r_M) - 1), r_l));
      r_l := (r_l + 1);
    }
    var r_z: int := read(r_b, (r_i + r_M) - 1) - read(r_b, r_i - 1);
    r_s := store(r_s, r_i, read(r_s, r_i - 1) + r_z);
    r_i := (r_i + 1);
  }
  assert(l_s == r_s);
 }
