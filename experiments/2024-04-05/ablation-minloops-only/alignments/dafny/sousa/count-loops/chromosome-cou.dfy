
function read(arr: int, index: int): real

function store(arr: int, index: int, value: real): int

method Main(l_o1_scores: int, l_o2_scores: int, r_o1_scores: int, r_o2_scores: int)
  decreases *
 {
  assume((l_o1_scores == r_o2_scores) && (l_o2_scores == r_o1_scores));
  var l_ret: int := -999;
  var l_comp: int := 0;
  var l_i: int := 0;
  var r_ret: int := -999;
  var r_comp: int := 0;
  var r_i: int := 0;
  while ((l_i < 5) && (r_i < 5))
    decreases *
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_ret == -999
    invariant l_ret <= -999
    invariant l_ret >= -999
    invariant l_comp == 0
    invariant l_comp <= 0
    invariant l_comp >= 0
    invariant l_i >= 0
    invariant r_ret == -999
    invariant r_ret <= -999
    invariant r_ret >= -999
    invariant r_comp == 0
    invariant r_comp <= 0
    invariant r_comp >= 0
  {
    if (read(l_o1_scores, l_i) < read(l_o2_scores, l_i)) {
      l_comp := (-1);
    } else {
      if (read(l_o2_scores, l_i) < read(l_o1_scores, l_i)) {
        l_comp := 1;
      } else {
        l_comp := 0;
      }
    }
    if (l_comp != 0) {
      l_ret := l_comp;
      break;
    }
    if (read(r_o1_scores, r_i) < read(r_o2_scores, r_i)) {
      r_comp := (-1);
    } else {
      if (read(r_o2_scores, r_i) < read(r_o1_scores, r_i)) {
        r_comp := 1;
      } else {
        r_comp := 0;
      }
    }
    l_i := (l_i + 1);
    if (r_comp != 0) {
      r_ret := r_comp;
      break;
    }
    r_i := (r_i + 1);
  }
  while (l_i < 5)
    decreases *
    invariant l_ret <= l_comp
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_ret != 0
    invariant l_i >= 0
    invariant r_ret == -999
    invariant r_ret <= -999
    invariant r_ret >= -999
    invariant r_comp == 0
    invariant r_comp <= 0
    invariant r_comp >= 0
  {
    if (read(l_o1_scores, l_i) < read(l_o2_scores, l_i)) {
      l_comp := (-1);
    } else {
      if (read(l_o2_scores, l_i) < read(l_o1_scores, l_i)) {
        l_comp := 1;
      } else {
        l_comp := 0;
      }
    }
    if (l_comp != 0) {
      l_ret := l_comp;
      break;
    }
    l_i := (l_i + 1);
  }
  while (r_i < 5)
    decreases *
    invariant l_ret <= l_comp
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_ret != 0
    invariant l_i >= 0
    invariant r_ret == -999
    invariant r_ret <= -999
    invariant r_ret >= -999
    invariant r_comp == 0
    invariant r_comp <= 0
    invariant r_comp >= 0
  {
    if (read(r_o1_scores, r_i) < read(r_o2_scores, r_i)) {
      r_comp := (-1);
    } else {
      if (read(r_o2_scores, r_i) < read(r_o1_scores, r_i)) {
        r_comp := 1;
      } else {
        r_comp := 0;
      }
    }
    if (r_comp != 0) {
      r_ret := r_comp;
      break;
    }
    r_i := (r_i + 1);
  }
  if (l_ret == (-999)) {
    l_ret := 0;
  }
  if (r_ret == (-999)) {
    r_ret := 0;
  }
  assert(l_ret == (-1 * r_ret));
 }
