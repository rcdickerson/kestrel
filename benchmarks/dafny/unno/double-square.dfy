method main(l_x : int, r_x : int)  
{
  assume l_x == r_x;
  var l_z := 0;
  var l_y := 0;
  l_z := (2 * l_x);
  var r_z := 0;
  var r_y := 0;
  r_z := r_x;
  while ((l_z > 0) && (r_z > 0))
  invariant l_z == 2 * r_z
  invariant l_y == 2 * r_y
  {
    l_z := (l_z - 1);
    l_y := (l_y + l_x);
    if (l_z > 0) {
      l_z := (l_z - 1);
      l_y := (l_y + l_x);
    }
    r_z := (r_z - 1);
    r_y := (r_y + r_x);
  }
  r_y := (2 * r_y);
  assert l_y == r_y;
}