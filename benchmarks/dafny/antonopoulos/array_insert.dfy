method main(l_A : array<int>, r_A : array<int>, l_val : int, r_val : int) 
modifies l_A 
modifies r_A
{
  assume l_val > 0;
  assume r_val > 0;
  assume l_A.Length == r_A.Length;
  assume l_A.Length > 0;

  var A_SIZE := l_A.Length - 1;
  var l_i := 0;

  while ((l_i < A_SIZE) && (l_A[l_i] < l_val)) 
  invariant (A_SIZE >= 0) ==> 0 <= l_i <= A_SIZE
  invariant (A_SIZE < 0) ==> l_i == 0
  {
    l_i := (l_i + 1);
  }
  var r_j := 0;
  var l_len := A_SIZE + 1;
  l_A[l_i] := l_val;
  while ((r_j < A_SIZE) && (r_A[r_j] < r_val)) 
  invariant (A_SIZE >= 0) ==> 0 <= r_j <= A_SIZE
  invariant (A_SIZE < 0) ==> r_j == 0
  {
    r_j := (r_j + 1);
  }
  var r_len := A_SIZE + 1;
  r_A[r_j] := r_val;
  while ((l_i < l_len) && (r_j < r_len))
  invariant l_len == r_len 
  invariant l_len >= 0
  invariant 0 <= l_i <= l_len 
  invariant 0 <= r_j <= r_len
  {
    l_i := (l_i + 1);
    r_j := (r_j + 1);
  }
  while (l_i < l_len && !(r_j < r_len)) 
  invariant l_len == r_len
  invariant l_len >= 0
  invariant (l_i < l_len) ==> r_j == r_len 
  invariant 0 <= l_i <= l_len 
  {
    l_i := (l_i + 1);
  }
  while (r_j < r_len && !(l_i < l_len)) 
  invariant l_len == r_len
  invariant (r_j < r_len) ==> l_i == l_len 
  invariant 0 <= r_j <= r_len 
  {
    r_j := (r_j + 1);
  }
  assert l_i == r_j;
 }
