method main(a_1 : array<int>, a_2 : array2<int>, f : array<int>, n : int)
  modifies a_1
  modifies a_2
 {
  assume a_1 != f;    
  assume a_1.Length == f.Length; 
  assume a_1.Length == a_2.Length0 * a_2.Length1; //Length0 is n, Length1 is m
  assume n >= 0;
  assume a_2.Length0 == 2 * n;
  assume a_1.Length <= 1000;

  var N := a_2.Length0;
  var M := a_2.Length1;
  var r_i := 0;
  var l_x := 0;
  while ((l_x < (N * M)) && (r_i < N))
    invariant 0 <= 2 * l_x <= N  
    //invariant (N % 2 == 1) ==> 0 <= 2 * l_x <= (N + 1)
    invariant 0 <= r_i <= N
    invariant r_i == l_x + l_x
    //invariant (N %2 == 1 && r_i < N) ==> r_i == l_x + l_x  
    //invariant forall i :: 0 <= i < l_x ==> a_1[i] == a_2[i/M,i % M]  
    invariant forall i :: 0 <= i < N  ==> forall j :: 0 <= j < M ==> i * M + j < l_x ==> a_1[i * M + j] == a_2[i,j]
    invariant forall i :: 0 <= i < l_x ==> a_1[i] == f[i] 
    invariant forall i :: 0 <= i < N  ==> forall j :: 0 <= j < M ==> i * M + j < (r_i * M) ==> f[i * M + j] == a_2[i,j]
    //invariant forall i :: 0 <= i < (r_i * M) ==> a_2[i /M,i % M] == f[i]
  {
    a_1[l_x] := f[l_x];
    l_x := (l_x + 1);
    var r_j := 0;
    while (r_j < M) 
      invariant 0 <= r_j <= M
      invariant  0 <= r_i <= N
      invariant !(r_i == 0 && r_j == 0) ==> forall i :: 0 <= i < N  ==> forall j :: 0 <= j < M ==> i * M + j < l_x ==> a_1[i * M + j] == a_2[i,j]
      //invariant !(r_i == 0 && r_j == 0) ==> forall i :: 0 <= i < l_x ==> a_1[i] == a_2[i/M,i%M]
      invariant forall i :: 0 <= i < l_x ==> a_1[i] == f[i]
      invariant forall i :: 0 <= i < N  ==> forall j :: 0 <= j < M ==> i * M + j < (r_i * M + r_j) ==> f[i * M + j] == a_2[i,j]
      //invariant forall i :: 0 <= i < (r_i * M + r_j) ==> a_2[i/M,i%M] == f[i]
    {
      a_2[r_i, r_j] := f[(r_i * M) + r_j];
      r_j := (r_j + 1);
    }
    r_i := (r_i + 1);
    if (r_i < N) 
    {
      var r_j := 0;
      while (r_j < M) 
        invariant 0 <= r_j <= M
        invariant 0 <= r_i <= N
        invariant forall i :: 0 <= i < N  ==> forall j :: 0 <= j < M ==> i * M + j < l_x ==> a_1[i * M + j] == a_2[i,j]
        //invariant forall i :: 0 <= i < l_x  ==> a_1[i] == a_2[i/M,i % M] 
        invariant forall i :: 0 <= i < l_x ==> a_1[i] == f[i]
        invariant forall i :: 0 <= i < N  ==> forall j :: 0 <= j < M ==> i * M + j < (r_i * M) ==> f[i * M + j] == a_2[i,j]  
        //invariant forall i :: 0 <= i < (r_i * M + r_j) ==> a_2[i/M,i%M] == f[i]
      {
        a_2[r_i, r_j] := f[(r_i * M) + r_j];
        r_j := (r_j + 1);
      }
      r_i := (r_i + 1);
    }
  }
  while ((l_x < (N * M)) && (!(r_i < N)))
   invariant /*(N % 2 == 0) ==> N/2*/ 0 <= l_x <= N * M 
   invariant /*(N %2 == 1) ==> (N + 1)/2*/ 0 <= l_x <= N * M 
   invariant r_i == N
   invariant forall i :: 0 <= i < N  ==> forall j :: 0 <= j < M ==> i * M + j < l_x ==> a_1[i * M + j] == a_2[i,j] 
   //invariant forall i :: 0 <= i < l_x ==> a_1[i] == a_2[i/M,i % M] 
   invariant forall i :: 0 <= i < l_x ==> a_1[i] == f[i]
  {
    a_1[l_x] := f[l_x];
    l_x := (l_x + 1);
  }

  assert forall i :: 0 <= i < N ==> forall j :: 0 <= j < M ==> a_1[i * M + j] == a_2[i,j];
 }