
method main(a_1 : array<int>, a_2 : array<int>)
  modifies a_1
  modifies a_2
 {    
  assume a_2.Length == a_1.Length;
  assume forall i :: 0 <= i < a_2.Length ==> a_2[i] == a_1[i];
  assume 0 < a_2.Length;

  var N := a_1.Length;
  var l_max := a_1[0];
  var l_maxi := 0;
  var l_i := 0;
  var r_j := 0;
  var r_max := 0;
  var r_maxi := 0;
  while ((l_i < N) && (r_j < N)) 
    invariant l_maxi < N
  {
    if (l_max < a_1[l_i]) {
      l_max := a_1[l_i];
      l_maxi := l_i;
    }
    l_i := (l_i + 1);
    if (r_j == 0) {
      r_max := a_2[0];
      r_maxi := 0;
    }
    if (r_max < a_2[r_j]) {
      r_max := a_2[r_j];
      r_maxi := r_j;
    }
    if (r_j == N) {
      var r_t := a_2[N];
      a_2[N] := r_max;
      a_2[r_maxi] := r_t;
    }
    r_j := (r_j + 1);
  }
/*    while ((l_i < N) && (!(r_j < N))) 
   invariant l_maxi < N
   {
     if (l_max < a_1[l_i]) {
       l_max := a_1[l_i];
       l_maxi := l_i;
     }
     l_i := (l_i + 1);
   }
   while ((!(l_i < N)) && (r_j < N)) {
     if (r_j == 0) {
       r_max := a_2[0];
       r_maxi := 0;
     }
     if (r_max < a_2[r_j]) {
       r_max := a_2[r_j];
       r_maxi := r_j;
     }
     if (r_j == N) {
       var r_t := a_2[N];
       a_2[N] := r_max;
       a_2[r_maxi] := r_t;
     }
     r_j := (r_j + 1);
   }
 */  var l_t := a_1[N-1];
  a_1[N-1] := l_max;
  a_1[l_maxi] := l_t; 
 assert forall i :: 0 <= i < a_2.Length ==> a_2[i] == a_1[i];
 }