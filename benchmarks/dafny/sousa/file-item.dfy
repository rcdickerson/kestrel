method Testing(l_o1_null: bool, 
  l_o2_null: bool,
  l_o1_fileName_null: bool,
  l_o2_fileName_null: bool,
  l_o1_fileName: int,
  l_o2_fileName: int,
  r_o1_null: bool,
  r_o2_null: bool,
  r_o1_fileName_null: bool,
  r_o2_fileName_null: bool, 
  r_o1_fileName: int, 
  r_o2_fileName: int) {
  assume((l_o1_null == r_o2_null) && ((l_o1_fileName_null == r_o2_fileName_null) && ((l_o1_fileName == r_o2_fileName) && ((l_o2_null == r_o1_null) && ((l_o2_fileName_null == r_o1_fileName_null) && (l_o2_fileName == r_o1_fileName))))));
  var l_result: int := -999;
  if (l_o1_null) {
    if (l_o2_null) {
      l_result := 0;
    } else {l_result := 1;
    }
  } else {if (l_o2_null) {
      l_result := (-1);
    }
  }
  if (l_result == (-999)) {
    var l_n1 : int := l_o1_fileName;
    var l_n2: int := l_o2_fileName;
    if (l_o1_fileName_null) {
      if (l_o2_fileName_null) {
        l_result := 0;
      } else {l_result := 1;
      }
    } else {if (l_o2_fileName_null) {
        l_result := (-1);
      }
    }
    l_result := (l_n1 - l_n2);
  }
  var r_result : int := -999;
  if (r_o1_null) {
    if (r_o2_null) {
      r_result := 0;
    } else {r_result := 1;
    }
  } else {if (r_o2_null) {
      r_result := (-1);
    }
  }
  if (r_result == (-999)) {
    var r_n1: int := r_o1_fileName;
    var r_n2: int := r_o2_fileName;
    if (r_o1_fileName_null) {
      if (r_o2_fileName_null) {
        r_result := 0;
      } else {r_result := 1;
      }
    } else {if (r_o2_fileName_null) {
        r_result := (-1);
      }
    }
    r_result := (r_n1 - r_n2);
  }
  assert(l_result == (-1 * r_result));
 }