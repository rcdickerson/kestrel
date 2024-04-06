
function two_exp(x: int, y: int): int

method Main(l_low: int, l_h: int, r_low: int, r_h: int)
  decreases *
 {
  assume((l_low == r_low) && ((l_low > l_h) && ((l_h > 0) && ((r_low > r_h) && ((r_h > 0) && ((two_exp(0, 1) == 1) && (forall x: int, y: int, xp1: int, ypy: int :: ((!((two_exp(x, y) == 1) && ((xp1 == (x + 1)) && (ypy == (y + y))))) || (two_exp(xp1, ypy) == 1)) && forall x1: int, y1: int, x2: int, y2: int :: ((!((two_exp(x1, y1) == 1) && (two_exp(x2, y2) == 1))) || (y1 == y2)))))))));
  var l_i: int := 0;
  var l_y: int := 1;
  var l_v: int := 0;
  var r_i: int := 0;
  var r_y: int := 1;
  var r_v: int := 0;
  while ((l_h > l_i) && (r_h > r_i))
    decreases *
    invariant two_exp(r_i, r_y) == 1
    invariant two_exp(l_i, l_y) == 1
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_i >= 0
    invariant l_v == 0
    invariant l_v <= 0
    invariant l_v >= 0
    invariant r_v == 0
    invariant r_v <= 0
    invariant r_v >= 0
  {
    l_i := (l_i + 1);
    l_y := (l_y + l_y);
    r_i := (r_i + 1);
    r_y := (r_y + r_y);
  }
  while (l_h > l_i)
    decreases *
    invariant two_exp(r_i, r_y) == 1
    invariant two_exp(l_i, l_y) == 1
    invariant l_i != 0
    invariant l_v == 0
    invariant l_v <= 0
    invariant l_v >= 0
    invariant r_i != 0
    invariant r_y >= 0
    invariant r_v == 0
    invariant r_v <= 0
    invariant r_v >= 0
    invariant l_i >= r_i
  {
    l_i := (l_i + 1);
    l_y := (l_y + l_y);
  }
  while (r_h > r_i)
    decreases *
    invariant two_exp(r_i, r_y) == 1
    invariant two_exp(l_i, l_y) == 1
    invariant l_i != 0
    invariant l_y >= 0
    invariant l_v == 0
    invariant l_v <= 0
    invariant l_v >= 0
    invariant r_i != 0
    invariant r_v == 0
    invariant r_v <= 0
    invariant r_v >= 0
  {
    r_i := (r_i + 1);
    r_y := (r_y + r_y);
  }
  l_v := 1;
  r_v := 1;
  while ((l_low > l_i) && (r_low > r_i))
    decreases *
    invariant two_exp(l_i, l_y) == 1
    invariant two_exp(r_i, r_y) == 1
    invariant l_i != 0
    invariant l_v == 1
    invariant l_v <= 1
    invariant l_v >= 1
    invariant r_i != 0
    invariant r_v == 1
    invariant r_v <= 1
    invariant r_v >= 1
  {
    l_i := (l_i + 1);
    l_y := (l_y + l_y);
    r_i := (r_i + 1);
    r_y := (r_y + r_y);
  }
  while (l_low > l_i)
    decreases *
    invariant two_exp(l_i, l_y) == 1
    invariant two_exp(r_i, r_y) == 1
    invariant l_i != 0
    invariant l_v == 1
    invariant l_v <= 1
    invariant l_v >= 1
    invariant r_i != 0
    invariant r_y >= 0
    invariant r_v == 1
    invariant r_v <= 1
    invariant r_v >= 1
  {
    l_i := (l_i + 1);
    l_y := (l_y + l_y);
  }
  while (r_low > r_i)
    decreases *
    invariant two_exp(r_i, r_y) == 1
    invariant two_exp(l_i, l_y) == 1
    invariant l_i != 0
    invariant l_y >= 0
    invariant l_v == 1
    invariant l_v <= 1
    invariant l_v >= 1
    invariant r_i != 0
    invariant r_v == 1
    invariant r_v <= 1
    invariant r_v >= 1
  {
    r_i := (r_i + 1);
    r_y := (r_y + r_y);
  }
  assert(l_y == r_y);
 }
