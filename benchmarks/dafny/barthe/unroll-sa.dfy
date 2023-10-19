
method main(l_N : int, r_N : int) 
{
  assume l_N == r_N;
  var l_x : int := 0;
  var l_i : int := 0;
  var r_x : int := 0;
  var r_i : int := 1;
  while ((l_i <= l_N) && (r_i <= r_N))
  invariant (l_N >= 0) ==> 0 <= l_i <= l_N 
  invariant (r_N >= 1) ==> 1 <= r_i <= (r_N + 1)
  invariant (l_N <= 0) ==> l_x == r_x 
  invariant r_i == l_i + 1
  invariant (l_i == 0) ==> (l_x == r_x)
  invariant (0 < r_i <= r_N + 1) ==> r_x == l_x + l_i 
  {
    l_x := (l_x + l_i);
    l_i := (l_i + 1);
    r_x := (r_x + r_i);
    r_i := (r_i + 1);
  }
  while (l_i <= l_N && !(r_i <= r_N)) 
  invariant (l_N >= 0) ==> l_N <= l_i <= (l_N + 1) 
  invariant (l_N <= 0) ==> l_x == r_x 
  invariant (l_i == 0 || l_i == l_N + 1) ==> l_x == r_x
  invariant (l_N > 0 && l_i == l_N) ==> r_x == l_x + l_i
  {
    l_x := (l_x + l_i);
    l_i := (l_i + 1);
  }
  /*while (r_i <= r_N) {
    assume(!(l_i <= l_N));
    r_x = (r_x + r_i);
    r_i = (r_i + 1);
  }*/
  assert l_x == r_x;
 }
