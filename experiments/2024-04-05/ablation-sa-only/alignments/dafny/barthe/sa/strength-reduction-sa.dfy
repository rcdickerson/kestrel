
method Main(l_B: int, l_C: int, l_N: int, l_x_in: int, r_B: int, r_C: int, r_N: int, r_x_in: int)
  decreases *
 {
  assume((l_B == r_B) && ((l_C == r_C) && ((l_N == r_N) && (l_x_in == r_x_in))));
  var l_x: int := l_x_in;
  var l_i: int := 0;
  var l_j: int := 0;
  var r_x: int := r_x_in;
  var r_i: int := 0;
  var r_j: int := r_C;
  if (l_i < l_N) {
    l_j := ((l_i * l_B) + l_C);
    l_x := (l_x + l_j);
    l_i := (l_i + 1);
  }
  if (l_i < l_N) {
    l_j := ((l_i * l_B) + l_C);
    l_x := (l_x + l_j);
    l_i := (l_i + 1);
  }
  while ((l_i < l_N) && (r_i < r_N))
    decreases *
    invariant r_j == ((r_i * r_B) + r_C)
    invariant r_i >= 0
  {
    l_j := ((l_i * l_B) + l_C);
    l_x := (l_x + l_j);
    l_i := (l_i + 1);
    r_x := (r_x + r_j);
    r_j := (r_j + r_B);
    r_i := (r_i + 1);
    if (r_i < r_N) {
      r_x := (r_x + r_j);
      r_j := (r_j + r_B);
      r_i := (r_i + 1);
    }
  }
  while (l_i < l_N)
    decreases *
    invariant r_j == ((r_i * r_B) + r_C)
  {
    l_j := ((l_i * l_B) + l_C);
    l_x := (l_x + l_j);
    l_i := (l_i + 1);
  }
  if (r_i < r_N) {
    while (r_i < r_N) {
      r_x := (r_x + r_j);
      r_j := (r_j + r_B);
      r_i := (r_i + 1);
    }
  }
  assert(l_x == r_x);
 }
