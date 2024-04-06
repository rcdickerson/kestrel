
method Main(l_N: int, r_N: int)
  decreases *
 {
  assume((l_N == r_N) && (l_N > 0));
  var l_x: int := 0;
  var l_i: int := 0;
  while (l_i <= l_N)
    decreases *
    invariant l_x >= 0
    invariant l_i >= 0
  {
    l_x := (l_x + l_i);
    l_i := (l_i + 1);
  }
  var r_x: int := 0;
  var r_i: int := 1;
  while (r_i <= r_N)
    decreases *
    invariant l_i != 0
    invariant l_i >= 2
    invariant r_x >= 0
    invariant r_i != 0
    invariant r_i >= 1
  {
    r_x := (r_x + r_i);
    r_i := (r_i + 1);
  }
  assert(l_x == r_x);
 }
