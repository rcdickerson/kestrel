method main(l_a : int, l_b : int, r_a : int, r_b : int)
 {    
  assume l_a == r_a;
  assume l_b == r_b;

  var l_c := 0;
  var r_c := 0;
  var lo_a := l_a;
  var ro_a := r_a;
  while ((lo_a < l_b) && (ro_a < r_b)) 
   invariant lo_a == ro_a
   invariant l_c == r_c
  
  {
    l_c := (l_c + (lo_a * lo_a));
    lo_a := (lo_a + 1);
    r_c := (r_c + (ro_a * ro_a));
    ro_a := (ro_a + 1);
  }
 assert l_c == r_c; 
 }