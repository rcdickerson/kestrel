method main(l_n : int, r_n : int)
{
  assume l_n == r_n;
  var l_x := 0;
  var l_i := 0;
  var r_x := 0;
  var r_i := 0;
  while ((l_i <= l_n) && (r_i <= r_n))
  invariant l_x == r_x 
  {
    l_x := (l_x + 1);
    l_i := (l_i + 1);
    r_x := (r_x + 1);
    r_i := (r_i + 1);
  }
  assert l_x == r_x;
}