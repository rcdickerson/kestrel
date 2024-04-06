
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
  while ((l_i < l_z) && (r_i < r_z))
    decreases *
    invariant l_y == r_y
    invariant l_y <= r_y
    invariant l_y >= r_y
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_y >= 0
    invariant l_i >= 0
    invariant l_y >= l_i
    invariant (l_z - (2 * r_z)) == 0
    invariant (l_z - (2 * r_z)) <= 0
    invariant (l_z - (2 * r_z)) >= 0
  {
    l_y := (l_y + l_x);
    l_i := (l_i + 1);
    r_y := (r_y + r_x);
    r_i := (r_i + 1);
  }
  while (l_i < l_z)
    decreases *
    invariant r_z <= r_i
    invariant l_y >= r_y
    invariant (l_z - (2 * r_z)) == 0
    invariant (l_z - (2 * r_z)) <= 0
    invariant (l_z - (2 * r_z)) >= 0
    invariant l_i >= r_z
    invariant r_y >= r_z
  {
    l_y := (l_y + l_x);
    l_i := (l_i + 1);
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
