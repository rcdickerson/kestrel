
function read(arr: int, index: int): int

function store(arr: int, index: int, value: int): int

method Main(l_o1_in: int, l_len1_in: int, l_o2_in: int, l_len2_in: int, r_o1_in: int, r_len1_in: int, r_o2_in: int, r_len2_in: int)
  decreases *
 {
  assume((l_o1_in == r_o2_in) && ((l_len1_in == r_len2_in) && ((l_o2_in == r_o1_in) && ((l_len2_in == r_len1_in) && ((l_len1_in >= 0) && (l_len2_in >= 0))))));
  var l_o1: int := l_o1_in;
  var l_len1: int := l_len1_in;
  var l_o2: int := l_o2_in;
  var l_len2: int := l_len2_in;
  var l_ret: int := -999;
  var l_index: int;
  var l_aentry: int;
  var l_bentry: int;
  l_index := 0;
  while ((l_index < l_len1) && (l_index < l_len2))
    decreases *
    invariant l_ret == -999
    invariant l_ret <= -999
    invariant l_ret >= -999
    invariant l_index >= 0
  {
    l_aentry := read(l_o1, l_index);
    l_bentry := read(l_o2, l_index);
    if (l_aentry < l_bentry) {
      l_ret := (-1);
      break;
    }
    if (l_aentry > l_bentry) {
      l_ret := 1;
      break;
    }
    l_index := (l_index + 1);
  }
  var r_o1: int := r_o1_in;
  var r_len1: int := r_len1_in;
  var r_o2: int := r_o2_in;
  var r_len2: int := r_len2_in;
  var r_ret: int := -999;
  var r_index: int;
  var r_aentry: int;
  var r_bentry: int;
  r_index := 0;
  while ((r_index < r_len1) && (r_index < r_len2))
    decreases *
    invariant l_o1 == r_o2
    invariant l_o1 <= r_o2
    invariant l_o1 >= r_o2
    invariant l_len1 == r_len2
    invariant l_len1 <= r_len2
    invariant l_len1 >= r_len2
    invariant l_o2 == r_o1
    invariant l_o2 <= r_o1
    invariant l_o2 >= r_o1
    invariant l_len2 == r_len1
    invariant l_len2 <= r_len1
    invariant l_len2 >= r_len1
    invariant l_index >= r_index
    invariant l_ret != 0
    invariant l_index >= 0
    invariant r_ret == -999
    invariant r_ret <= -999
    invariant r_ret >= -999
  {
    r_aentry := read(r_o1, r_index);
    r_bentry := read(r_o2, r_index);
    if (r_aentry < r_bentry) {
      r_ret := (-1);
      break;
    }
    if (r_aentry > r_bentry) {
      r_ret := 1;
      break;
    }
    r_index := (r_index + 1);
  }
  if (l_ret == (-999)) {
    if (l_len1 < l_len2) {
      l_ret := (-1);
    }
    if (l_len1 > l_len2) {
      l_ret := 1;
    }
    l_ret := 0;
  }
  if (r_ret == (-999)) {
    if (r_len1 < r_len2) {
      r_ret := (-1);
    }
    if (r_len1 > r_len2) {
      r_ret := 1;
    }
    r_ret := 0;
  }
  assert(l_ret == (-1 * r_ret));
 }
