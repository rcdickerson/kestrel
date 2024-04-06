
method Main(l_x: int, r_x: int)
  decreases *
 {
  assume(l_x == r_x);
  var l_z: int := 0;
  var l_y: int := 0;
  l_z := (2 * l_x);
  while (l_z > 0) {
    l_z := (l_z - 1);
    l_y := (l_y + l_x);
  }
  var r_z: int := 0;
  var r_y: int := 0;
  r_z := r_x;
  while (r_z > 0)
    decreases *
    invariant l_z <= 0
  {
    r_z := (r_z - 1);
    r_y := (r_y + r_x);
  }
  r_y := (2 * r_y);
  assert(l_y == r_y);
 }
