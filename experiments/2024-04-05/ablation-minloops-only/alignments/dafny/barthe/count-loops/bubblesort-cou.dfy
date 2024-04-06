const epsilon: real := 0.01;

function read(list_id: int, index: int): real

function store(list_id: int, index: int, value: real): int

method Main(l_list_in: int, l_size_in: int, r_list_in: int, r_size_in: int)
  decreases *
 {
  assume((l_size_in == r_size_in) && (forall i: int, j: int, a: int, x: real :: ((!(i == j)) || (read(store(a, i, x), j) == x)) && (forall i: int, j: int, a: int, x: real :: ((!(i != j)) || (read(store(a, i, x), j) == read(a, j))) && forall i: int :: (((!(read(l_list_in, i) < read(r_list_in, i))) || ((read(r_list_in, i) - read(l_list_in, i)) < epsilon)) && ((!(read(l_list_in, i) >= read(r_list_in, i))) || ((read(l_list_in, i) - read(r_list_in, i)) < epsilon))))));
  var l_list: int := l_list_in;
  var l_size: int := l_size_in;
  var l_i: int := 0;
  var r_list: int := r_list_in;
  var r_size: int := r_size_in;
  var r_i: int := 0;
  while ((l_i < l_size) && (r_i < r_size))
    decreases *
    invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
    invariant l_size == r_size
    invariant l_size <= r_size
    invariant l_size >= r_size
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_i >= 0
  {
    var l_j: int := l_size - 1;
    var r_j: int := r_size - 1;
    while ((l_j > l_i) && (r_j > r_i))
      decreases *
      invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
      invariant l_size == r_size
      invariant l_size <= r_size
      invariant l_size >= r_size
      invariant l_i == r_i
      invariant l_i <= r_i
      invariant l_i >= r_i
      invariant l_j == r_j
      invariant l_j <= r_j
      invariant l_j >= r_j
      invariant l_size != 0
      invariant l_i >= 0
      invariant l_size > l_i
      invariant l_size > l_j
    {
      var l_prev: real := read(l_list, l_j - 1);
      var l_cur: real := read(l_list, l_j);
      var r_prev: real := read(r_list, r_j - 1);
      var r_cur: real := read(r_list, r_j);
      if (l_prev > l_cur) {
        var l_val: real := read(l_list, l_j);
        var l_prev_val: real := read(l_list, l_j - 1);
        l_list := store(l_list, l_j, l_prev_val);
        l_list := store(l_list, l_j - 1, l_val);
      }
      if (r_prev > r_cur) {
        var r_val: real := read(r_list, r_j);
        var r_prev_val: real := read(r_list, r_j - 1);
        r_list := store(r_list, r_j, r_prev_val);
        r_list := store(r_list, r_j - 1, r_val);
      }
      l_j := (l_j - 1);
      r_j := (r_j - 1);
    }
    if (l_j > l_i) {
      while (l_j > l_i)
        decreases *
        invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
      {
        var l_prev: real := read(l_list, l_j - 1);
        var l_cur: real := read(l_list, l_j);
        if (l_prev > l_cur) {
          var l_val: real := read(l_list, l_j);
          var l_prev_val: real := read(l_list, l_j - 1);
          l_list := store(l_list, l_j, l_prev_val);
          l_list := store(l_list, l_j - 1, l_val);
        }
        l_j := (l_j - 1);
      }
    }
    if (r_j > r_i) {
      while (r_j > r_i)
        decreases *
        invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
      {
        var r_prev: real := read(r_list, r_j - 1);
        var r_cur: real := read(r_list, r_j);
        if (r_prev > r_cur) {
          var r_val: real := read(r_list, r_j);
          var r_prev_val: real := read(r_list, r_j - 1);
          r_list := store(r_list, r_j, r_prev_val);
          r_list := store(r_list, r_j - 1, r_val);
        }
        r_j := (r_j - 1);
      }
    }
    l_i := (l_i + 1);
    r_i := (r_i + 1);
  }
  if (l_i < l_size) {
    while (l_i < l_size)
      decreases *
      invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
    {
      var l_j: int := l_size - 1;
      if (l_j > l_i) {
        while (l_j > l_i)
          decreases *
          invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
        {
          var l_prev: real := read(l_list, l_j - 1);
          var l_cur: real := read(l_list, l_j);
          if (l_prev > l_cur) {
            var l_val: real := read(l_list, l_j);
            var l_prev_val: real := read(l_list, l_j - 1);
            l_list := store(l_list, l_j, l_prev_val);
            l_list := store(l_list, l_j - 1, l_val);
          }
          l_j := (l_j - 1);
        }
      }
      l_i := (l_i + 1);
    }
  }
  if (r_i < r_size) {
    while (r_i < r_size)
      decreases *
      invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
    {
      var r_j: int := r_size - 1;
      if (r_j > r_i) {
        while (r_j > r_i)
          decreases *
          invariant forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon)))
        {
          var r_prev: real := read(r_list, r_j - 1);
          var r_cur: real := read(r_list, r_j);
          if (r_prev > r_cur) {
            var r_val: real := read(r_list, r_j);
            var r_prev_val: real := read(r_list, r_j - 1);
            r_list := store(r_list, r_j, r_prev_val);
            r_list := store(r_list, r_j - 1, r_val);
          }
          r_j := (r_j - 1);
        }
      }
      r_i := (r_i + 1);
    }
  }
  assert(forall j: int :: (((!(read(l_list, j) < read(r_list, j))) || ((read(r_list, j) - read(l_list, j)) < epsilon)) && ((!(read(l_list, j) >= read(r_list, j))) || ((read(l_list, j) - read(r_list, j)) < epsilon))));
 }
