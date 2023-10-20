method main(l_a : array<real>, r_a : array<real>, epsilon : real)
modifies l_a
modifies r_a 
{
  assume l_a != r_a;
  assume epsilon > 0.0;
  assume l_a.Length == r_a.Length;
  assume forall i :: 0 <= i < l_a.Length ==> (l_a[i] >= r_a[i] ==> (l_a[i] - r_a[i]) < epsilon) || (r_a[i] >= l_a[i] ==> (r_a[i] - l_a[i]) < epsilon);
 
  var N := l_a.Length;
  var r_i : int := 0;
  var l_i : int := 0;
  while ((l_i < N) && (r_i < N))
  invariant 0 <= l_i <= N
  invariant 0 <= r_i <= N 
  invariant l_i == r_i
  invariant forall i :: 0 <= i < N ==> (l_a[i] >= r_a[i] ==> (l_a[i] - r_a[i]) < epsilon) || (r_a[i] >= l_a[i] ==> (r_a[i] - l_a[i]) < epsilon)
  {
    var l_j : int := N - 1;
    while (l_j > l_i)
    invariant l_j >= l_i >= 0 
    invariant forall i :: l_j + 1 <= i < N ==> l_a[l_j] <= l_a[i]
    {
      if (l_a[l_j - 1] > l_a[l_j]) 
      {
        var l_temp : real := l_a[l_j];
        l_a[l_j] := l_a[l_j - 1];
        l_a[l_j - 1] := l_temp;
      }
      l_j := (l_j - 1);
    }
    l_i := (l_i + 1);
    var r_j : int := N - 1;
    while (r_j > r_i)
    invariant r_j >= r_i >= 0
    invariant forall i :: r_j + 1 <= i < N ==> r_a[r_j] <= r_a[i]  
    {
      if (r_a[r_j - 1] > r_a[r_j]) 
      {
        var r_temp : real := r_a[r_j];
        r_a[r_j] := r_a[r_j - 1];
        r_a[r_j - 1] := r_temp;
      }
      r_j := (r_j - 1);
    }
    r_i := (r_i + 1);
  }
  
  assert forall i :: 0 <= i < l_a.Length ==> (l_a[i] >= r_a[i] ==> (l_a[i] - r_a[i]) < epsilon) || (r_a[i] >= l_a[i] ==> (r_a[i] - l_a[i]) < epsilon);
 }
