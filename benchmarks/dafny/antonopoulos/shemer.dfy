method main(l_x : int, r_x : int)  
{
  assume l_x == r_x;
  var l_y := 0;
  var l_z := 2 * l_x;
  var l_i := 0;
  var r_y := 0;
  var r_z := r_x;
  var r_i := 0;
  while ((l_i < l_z) && (r_i < r_z))
  invariant l_y == 2 * r_y
  invariant l_i == 2 * r_i 
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
  r_y := (r_y * 2);
  assert l_y == r_y;
}