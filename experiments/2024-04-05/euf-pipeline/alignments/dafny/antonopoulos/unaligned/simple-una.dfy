
method Main(l_n: int, r_n: int)
  decreases *
 {
  assume(l_n == r_n);
  var l_x: int := 0;
  var l_i: int := 0;
  while (l_i <= l_n)
    decreases *
    invariant l_x >= 0
    invariant l_i >= 0
  {
    l_x := (l_x + 1);
    l_i := (l_i + 1);
  }
  var r_x: int := 0;
  var r_i: int := 0;
  while (r_i <= r_n)
    decreases *
    invariant r_x >= 0
    invariant r_i >= 0
  {
    r_x := (r_x + 1);
    r_i := (r_i + 1);
  }
  assert(l_x == r_x);
 }
