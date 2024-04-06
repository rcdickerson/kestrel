
method Main(l_x: int, r_x: int)
  decreases *
 {
  assume(l_x == r_x);
  var l_y: int := 0;
  var l_z: int := 2 * l_x;
  var l_i: int := 0;
  var r_y: int := 0;
  var r_z: int := r_x;
  var r_i: int := 0;
  if (l_i < l_z) {
    l_y := (l_y + l_x);
    l_i := (l_i + 1);
  }
  while ((l_i < l_z) && (r_i < r_z))
    decreases *
    invariant r_y >= 0
    invariant r_i >= 0
    invariant l_y >= r_z
    invariant (l_z - (2 * r_z)) == 0
    invariant (l_z - (2 * r_z)) <= 0
    invariant (l_z - (2 * r_z)) >= 0
    invariant (l_i - (2 * (r_i - 1))) >= 0
    invariant r_y >= r_i
  {
    l_y := (l_y + l_x);
    l_i := (l_i + 1);
    if (l_i < l_z) {
      l_y := (l_y + l_x);
      l_i := (l_i + 1);
    }
    r_y := (r_y + r_x);
    r_i := (r_i + 1);
  }
  if (l_i < l_z) {
    while (l_i < l_z) {
      l_y := (l_y + l_x);
      l_i := (l_i + 1);
    }
  }
  if (r_i < r_z) {
    while (r_i < r_z) {
      r_y := (r_y + r_x);
      r_i := (r_i + 1);
    }
  }
  r_y := (r_y * 2);
  assert(l_y == r_y);
 }
