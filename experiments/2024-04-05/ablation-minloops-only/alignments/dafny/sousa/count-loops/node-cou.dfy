
method Main(l_o1_contains_id: int, l_o1_get_id: int, l_o2_contains_id: int, l_o2_get_id: int, r_o1_contains_id: int, r_o1_get_id: int, r_o2_contains_id: int, r_o2_get_id: int)
  decreases *
 {
  assume((l_o1_contains_id == r_o2_contains_id) && ((l_o1_get_id == r_o2_get_id) && ((l_o2_contains_id == r_o1_contains_id) && (l_o2_get_id == r_o1_get_id))));
  var l_ret: int := -999;
  var r_ret: int := -999;
  if ((l_o1_contains_id != 0) && (l_o2_contains_id != 0)) {
    var l_order1: int := l_o1_get_id;
    var l_order2: int := l_o2_get_id;
    if (l_order1 < l_order2) {
      l_ret := (-1);
    } else {
      if (l_order1 > l_order2) {
        l_ret := 1;
      } else {
        l_ret := 0;
      }
    }
  }
  if ((r_o1_contains_id != 0) && (r_o2_contains_id != 0)) {
    var r_order1: int := r_o1_get_id;
    var r_order2: int := r_o2_get_id;
    if (r_order1 < r_order2) {
      r_ret := (-1);
    } else {
      if (r_order1 > r_order2) {
        r_ret := 1;
      } else {
        r_ret := 0;
      }
    }
  }
  if (l_ret == (-999)) {
    l_ret := (l_o1_get_id - l_o2_get_id);
  }
  if (r_ret == (-999)) {
    r_ret := (r_o1_get_id - r_o2_get_id);
  }
  assert(l_ret == (-1 * r_ret));
 }
