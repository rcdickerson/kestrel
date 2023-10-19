method main(a_1 : array<int>, a_2 : array<int>)
  modifies a_1
  modifies a_2
 {
  assume a_1 != a_2;    
  assume a_2.Length == a_1.Length;
  assume forall i :: 0 <= i < a_2.Length ==> a_2[i] == a_1[i];
  assume 0 < a_2.Length;

  var N := a_2.Length - 1;
  var l_max := a_1[0];
  var l_maxi := 0;
  var l_i := 0;
  var r_j := 0;
  var r_max := 0;
  var r_maxi := 0;
  while ((l_i <= N) && (r_j <= N))
        invariant 0 <= l_i <= (N + 1)  
        invariant 0 <= r_j <= (N + 1)
        invariant l_i == r_j
        invariant (l_i > 0) ==> l_max == r_max 
        invariant l_maxi == r_maxi
        invariant (l_i == 0) ==> l_maxi == 0
        invariant (l_i == 0) ==> r_maxi == 0
        invariant (l_i > 0) ==> 0 <= l_maxi < l_i 
        invariant (l_i > 0) ==> 0 <= r_maxi < r_j
        invariant (r_j <= N) ==> forall i :: 0 <= i <= N ==> a_1[i] == a_2[i]
        invariant (r_j == N + 1) ==> forall i :: 0 <= i < r_maxi ==> a_1[i] == a_2[i]
        invariant (r_j == N + 1) ==> forall i :: (r_maxi + 1) <= i < N ==> a_1[i] == a_2[i]
        invariant l_max == a_1[l_maxi] 
        invariant (0 < r_j <= N) ==> r_max == a_2[r_maxi]
        invariant (r_j == N + 1) ==> r_max == a_2[N]
        invariant (r_j == N + 1) ==> a_1[r_maxi] == a_2[N]
        invariant (r_j == N + 1) ==> a_1[N] == a_2[r_maxi]
  {
    if (l_max < a_1[l_i]) {
      l_max := a_1[l_i];
      l_maxi := l_i;
    }
    if(r_j == 0) {
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
    l_i := (l_i + 1);
  }
  var l_t := a_1[N];
  a_1[N] := l_max;
  a_1[l_maxi] := l_t; 
 assert forall i :: 0 <= i < a_2.Length ==> a_2[i] == a_1[i];
 }