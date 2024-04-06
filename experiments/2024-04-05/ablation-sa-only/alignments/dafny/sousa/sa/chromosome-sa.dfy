
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
  if (r_i < 5) {
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
  if (r_i < 5) {
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
  while ((l_i < 5) && (r_i < 5))
    decreases *
    invariant l_o1 != 0
    invariant l_len1 != 0
    invariant l_o2 != 0
    invariant l_len2 != 0
    invariant l_ret == -999
    invariant l_ret <= -999
    invariant l_ret >= -999
    invariant l_index == 0
    invariant l_index <= 0
    invariant l_index >= 0
    invariant l_o1 != l_len1
    invariant l_o1 != l_o2
    invariant l_o1 != l_len2
    invariant l_o1 != l_index
    invariant l_len1 != l_o2
    invariant l_len1 != l_len2
    invariant l_len1 > l_index
    invariant l_o2 != l_len2
    invariant l_o2 != l_index
    invariant l_len2 > l_index
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
    if (r_i < 5) {
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
  }
  while (l_i < 5)
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
    invariant l_index == r_index
    invariant l_index <= r_index
    invariant l_index >= r_index
    invariant l_o1 != 0
    invariant l_len1 != 0
    invariant l_o2 != 0
    invariant l_len2 != 0
    invariant l_ret != 0
    invariant l_index == 0
    invariant l_index <= 0
    invariant l_index >= 0
    invariant l_aentry != 0
    invariant l_bentry != 0
    invariant r_ret == -999
    invariant r_ret <= -999
    invariant r_ret >= -999
    invariant l_o1 != l_len1
    invariant l_o1 != l_o2
    invariant l_o1 != l_len2
    invariant l_o1 != l_index
    invariant l_o1 != l_aentry
    invariant l_o1 != l_bentry
    invariant l_len1 != l_o2
    invariant l_len1 != l_len2
    invariant l_len1 > l_index
    invariant l_len1 != l_aentry
    invariant l_len1 != l_bentry
    invariant l_o2 != l_len2
    invariant l_o2 != l_index
    invariant l_o2 != l_aentry
    invariant l_o2 != l_bentry
    invariant l_len2 > l_index
    invariant l_len2 != l_aentry
    invariant l_len2 != l_bentry
    invariant l_index != l_aentry
    invariant l_index != l_bentry
    invariant l_aentry != l_bentry
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
  if (r_i < 5) {
    while (r_i < 5) {
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
  }
  if (l_ret == (-999)) {
    l_ret := 0;
  }
  if (r_ret == (-999)) {
    r_ret := 0;
  }
  assert(l_ret == (-1 * r_ret));
 }
