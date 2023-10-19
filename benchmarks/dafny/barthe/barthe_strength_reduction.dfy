method main(l_B : int, l_C : int, l_N : int, l_x : int, r_B : int, r_C : int, r_N : int, r_x : int)
 {    
  assume l_B == r_B;
  assume l_C == r_C;
  assume l_N == r_N;
  assume l_x == r_x;

  var l_i := 0;
  var l_j := 0;
  var r_i := 0;
  var r_j := r_C;
  var l_xo := l_x;
  var r_xo := r_x;
  while ((l_i < l_N) && (r_i < r_N))
   invariant l_i == r_i
   invariant l_xo == r_xo
   invariant r_i == 0 ==> r_j == r_C
   invariant r_i > 0 ==> r_j == r_i * r_B + r_C  
  
  {
    l_j := ((l_i * l_B) + l_C);
    l_xo := (l_xo + l_j);
    l_i := (l_i + 1);
    r_xo := (r_xo + r_j);
    r_j := (r_j + r_B);
    r_i := (r_i + 1);
  }
 assert l_xo == r_xo; 
 }