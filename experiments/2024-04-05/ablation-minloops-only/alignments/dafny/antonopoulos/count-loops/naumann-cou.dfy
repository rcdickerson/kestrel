
method Main(l_x: int, r_x: int)
  decreases *
 {
  assume(l_x == r_x);
  var l_y: int := l_x;
  var l_z: int := 24;
  var l_w: int := 0;
  var r_y: int := r_x;
  var r_z: int := 16;
  var r_w: int := 0;
  while ((l_y > 4) && (r_y > 4))
    decreases *
    invariant l_w >= 0
    invariant r_w >= 0
  {
    if ((l_w % 2) == 0) {
      l_z := (l_z * l_y);
      l_y := (l_y - 1);
    }
    if ((r_w % 3) == 0) {
      r_z := (r_z * 2);
      r_y := (r_y - 1);
    }
    l_w := (l_w + 1);
    r_w := (r_w + 1);
  }
  if (l_y > 4) {
    while (l_y > 4) {
      if ((l_w % 2) == 0) {
        l_z := (l_z * l_y);
        l_y := (l_y - 1);
      }
      l_w := (l_w + 1);
    }
  }
  while (r_y > 4)
    decreases *
    invariant l_y <= 4
  {
    if ((r_w % 3) == 0) {
      r_z := (r_z * 2);
      r_y := (r_y - 1);
    }
    r_w := (r_w + 1);
  }
  assert(l_z > r_z);
 }
