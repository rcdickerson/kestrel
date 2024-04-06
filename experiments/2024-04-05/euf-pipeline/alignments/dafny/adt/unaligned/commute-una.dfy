
function f(x: int): int

function g(x: int): int

method Main(l_n: int, r_n: int)
  decreases *
 {
  assume(forall i: int :: (f(g(i)) == g(f(i))) && (l_n == r_n));
  var l_sum: int := 0;
  var l_i: int := 0;
  while (l_i < l_n)
    decreases *
    invariant l_i >= 0
  {
    var l_result: int := f(l_i);
    l_result := g(l_result);
    l_sum := (l_sum + l_result);
    l_i := (l_i + 1);
  }
  var r_sum: int := 0;
  var r_i: int := 0;
  while (r_i < r_n)
    decreases *
    invariant r_i >= 0
  {
    var r_result: int := g(r_i);
    r_result := f(r_result);
    r_sum := (r_sum + r_result);
    r_i := (r_i + 1);
  }
  assert(l_sum == r_sum);
 }
