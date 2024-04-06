
method Main(l_a_in: int, l_b_in: int, r_a_in: int, r_b_in: int)
  decreases *
 {
  assume((l_a_in == r_a_in) && (l_b_in == r_b_in));
  var l_a: int := l_a_in;
  var l_b: int := l_b_in;
  var l_c: int := 0;
  while (l_a < l_b)
    decreases *
    invariant l_c >= 0
  {
    l_c := (l_c + (l_a * l_a));
    l_a := (l_a + 1);
  }
  var r_a: int := r_a_in;
  var r_b: int := r_b_in;
  var r_c: int := 0;
  while (r_a < r_b)
    decreases *
    invariant l_a >= l_b
    invariant l_a >= r_b
    invariant r_c >= 0
  {
    r_c := (r_c + (r_a * r_a));
    r_a := (r_a + 1);
  }
  assert(l_c == r_c);
 }
