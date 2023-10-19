method main(l_a : array<int>, l_b : array<int>, l_c : array<int>,
r_a : array<int>, r_b : array<int>, r_c : array<int>)
  modifies l_a
  modifies l_b
  modifies l_c
  modifies r_a
  modifies r_b
  modifies r_c
 {
    //Lengths are same
  assume l_a.Length == l_b.Length; 
  assume l_b.Length == l_c.Length;
  assume l_c.Length == r_a.Length;
  assume r_a.Length == r_b.Length;
  assume r_b.Length == r_c.Length;

  //ensure arrays don't alias each other
  assume l_a != l_b; 
  assume l_a != l_c;
  assume l_a != r_a;
  assume l_a != r_b;
  assume l_a != r_c;

  assume l_b != l_c;
  assume l_b != r_a;
  assume l_b != r_b;
  assume l_b != r_c;

  assume l_c != r_a;
  assume l_c != r_b;
  assume l_c != r_c;

  assume r_a != r_b;
  assume r_a != r_c;
  assume r_b != r_c;


  //elements are all equal for respective arrays
  assume forall i :: 0 <= i < l_a.Length ==> l_a[i] == r_a[i];
  assume forall i :: 0 <= i < l_a.Length ==> l_b[i] == r_b[i];
  assume forall i :: 0 <= i < l_a.Length ==> l_c[i] == r_c[i];
  assume r_a.Length % 2 == 0;

  assume 2 <= r_a.Length <= 4;

  var r_j := 0;
  var N := l_a.Length;

  r_a[0] := (r_a[0] + 1);
  r_b[0] := (r_b[0] + r_a[0]);
  r_a[1] := (r_a[1] + 1);
  var l_i := 0;
  while ((l_i < N) && (r_j < (N - 2))) 
   invariant 0 <= l_i <= N 
   invariant /*(N % 2 == 0) ==>*/ 0 <= 2 * r_j <= N 
   //invariant (N % 2 == 1) ==> 0 <= r_j <= (N + 1)/2
   invariant /*(N % 2 == 0) ==>*/ l_i == r_j + r_j 
   //invariant (N %2 == 1 && l_i < N) ==> l_i == r_j + r_j 
   invariant (r_j < 2) ==> forall i :: 0 <= i < l_i ==> l_a[i] == r_a[i]
   invariant (r_j < 2 && (r_j + 2) <= N) ==> forall i :: l_i <= i < (r_j + 2) ==> l_a[i] + 1 == r_a[i]
   invariant (r_j < 2 && (r_j + 2) > N) ==> forall i :: l_i <= i < N ==> l_a[i] + 1 == r_a[i]
   invariant (r_j < 2) ==> forall i :: (r_j + 2) <= i < N ==> l_a[i] == r_a[i]
   invariant (r_j >= 2 && (r_j + 2) <= N) ==> forall i :: 0 <= i < (r_j + 2) ==> l_a[i] == r_a[i]
   invariant (r_j >= 2 && (r_j + 2) > N) ==> forall i :: 0 <= i < N ==> l_a[i] == r_a[i]
   invariant (r_j >= 2) ==> forall i :: (r_j + 2) <= i < l_i ==> r_a[i] + 1 == l_a[i]
   invariant (r_j >= 2) ==> forall i :: l_i <= i < N ==> l_a[i] == r_a[i]
   invariant (r_j == 0) ==> forall i :: 0 <= i < r_j ==> l_b[i] == r_b[i]
   invariant (r_j == 0) ==> forall i :: 0 <= i < (r_j + 1) ==> l_b[i] + l_a[i] + 1 == r_b[i]
   invariant (r_j == 0) ==> forall i :: (r_j + 1) <= i < N ==> l_b[i] == r_b[i]
   invariant (r_j >= 1 && (r_j + 1) <= N) ==> forall i :: 0 <= i < (r_j + 1) ==> l_b[i] == r_b[i]
   invariant (r_j >= 1 && (r_j + 1) > N) ==> forall i :: 0 <= i < N ==> l_b[i] == r_b[i]
   invariant (r_j >= 1) ==> forall i :: (r_j + 1) <= i < l_i ==> r_b[i] + r_a[i]  == l_b[i]
   //invariant (r_j >= 1) ==> forall i :: (r_j + 1) <= i < l_i ==> (r_b[i] == l_b[i] || r_b[i] != l_b[i])
   invariant (r_j >= 1) ==> forall i :: l_i <= i < N ==> l_b[i] == r_b[i]
   invariant forall i :: 0 <= i < r_j ==> l_c[i] == r_c[i]
   invariant forall i :: r_j <= i < l_i ==> r_c[i] + r_b[i] == l_c[i]
   //invariant forall i :: r_j <= i < l_i ==> (r_c[i] == l_c[i] || r_c[i] != l_c[i])
   invariant forall i :: l_i <= i < N ==> l_c[i] == r_c[i]
  {
    l_a[l_i] := (l_a[l_i] + 1);
    l_b[l_i] := (l_b[l_i] + l_a[l_i]);
    l_c[l_i] := (l_c[l_i] + l_b[l_i]);
    l_i := (l_i + 1);
    if (l_i < N) {
      l_a[l_i] := (l_a[l_i] + 1);
      l_b[l_i] := (l_b[l_i] + l_a[l_i]);
      l_c[l_i] := (l_c[l_i] + l_b[l_i]);
      l_i := (l_i + 1);
    }
    r_a[r_j + 2] := (r_a[r_j + 2] + 1);
    r_b[r_j + 1] := (r_b[r_j + 1] + r_a[r_j + 1]);
    r_c[r_j] := (r_c[r_j] + r_b[r_j]);
    r_j := (r_j + 1);
  }
  /*while ((l_i < 10) && (!(r_j < (10 - 2)))) {
    l_a[l_i] = (l_a[l_i] + 1);
    l_b[l_i] = (l_b[l_i] + l_a[l_i]);
    l_c[l_i] = (l_c[l_i] + l_b[l_i]);
    l_i = (l_i + 1);
  }*/
  while ((!(l_i < N)) && (r_j < (N - 2))) 
    invariant 0 <= r_j <= (N - 2)
    invariant (r_j + 2 <= N) ==> forall i :: 0 <= i < (r_j + 2) ==> l_a[i] == r_a[i]
    invariant (r_j + 2 > N) ==> forall i :: 0 <= i < N ==> l_a[i] == r_a[i]
    invariant forall i :: (r_j + 2) <= i < l_i ==> r_a[i] + 1 == l_a[i]
    invariant forall i :: l_i <= i < N ==> l_a[i] == r_a[i]
    invariant (r_j + 1 <= N) ==> forall i :: 0 <= i < (r_j + 1) ==> l_b[i] == r_b[i]
    invariant (r_j + 1 > N) ==> forall i :: 0 <= i < N ==> l_b[i] == r_b[i]
    //invariant (r_j >= 1) ==> forall i :: (r_j + 1) <= i < l_i ==> (r_b[i] == l_b[i] || r_b[i] != l_b[i])
    invariant forall i :: (r_j + 1) <= i < l_i ==> r_b[i] + r_a[i] == l_b[i]
    invariant forall i :: l_i <= i < N ==> l_b[i] == r_b[i]
    invariant forall i :: 0 <= i < r_j ==> l_c[i] == r_c[i]
    invariant forall i :: r_j <= i < l_i ==> r_c[i] + r_b[i] == l_c[i]
    //invariant forall i :: r_j <= i < l_i ==> (r_c[i] == l_c[i] || r_c[i] != l_c[i])
    invariant forall i :: l_i <= i < N ==> l_c[i] == r_c[i]
  {
    r_a[r_j + 2] := (r_a[r_j + 2] + 1);
    r_b[r_j + 1] := (r_b[r_j + 1] + r_a[r_j + 1]);
    r_c[r_j] := (r_c[r_j] + r_b[r_j]);
    r_j := (r_j + 1);
  }
  r_c[r_j] := (r_c[r_j] + r_b[r_j]);
  r_b[r_j + 1] := (r_b[r_j + 1] + r_a[r_j + 1]);
  r_c[r_j + 1] := (r_c[r_j + 1] + r_b[r_j + 1]);

  //elements are all equal for respective arrays
  assert forall i :: 0 <= i < N ==> l_a[i] == r_a[i];
  assert forall i :: 0 <= i < N ==> l_b[i] == r_b[i];
  assert forall i :: 0 <= i < N ==> l_c[i] == r_c[i];


 }