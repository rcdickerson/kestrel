
method Main(l_o1_score: int, l_o1_seq1start: int, l_o1_seq2start: int, l_o2_score: int, l_o2_seq1start: int, l_o2_seq2start: int, r_o1_score: int, r_o1_seq1start: int, r_o1_seq2start: int, r_o2_score: int, r_o2_seq1start: int, r_o2_seq2start: int)
  decreases *
 {
  assume((l_o1_score == r_o2_score) && ((l_o1_seq1start == r_o2_seq1start) && ((l_o1_seq2start == r_o2_seq2start) && ((l_o2_score == r_o1_score) && ((l_o2_seq1start == r_o1_seq1start) && (l_o2_seq2start == r_o1_seq2start))))));
  var l_ret: int;
  if (l_o1_score > l_o2_score) {
    l_ret := (-1);
  } else {
    if (l_o1_score < l_o2_score) {
      l_ret := 1;
    } else {
      if ((l_o1_seq1start + l_o1_seq2start) < (l_o2_seq1start + l_o2_seq2start)) {
        l_ret := (-1);
      } else {
        if ((l_o1_seq1start + l_o1_seq2start) > (l_o2_seq1start + l_o2_seq2start)) {
          l_ret := 1;
        } else {
          l_ret := 0;
        }
      }
    }
  }
  var r_ret: int;
  if (r_o1_score > r_o2_score) {
    r_ret := (-1);
  } else {
    if (r_o1_score < r_o2_score) {
      r_ret := 1;
    } else {
      if ((r_o1_seq1start + r_o1_seq2start) < (r_o2_seq1start + r_o2_seq2start)) {
        r_ret := (-1);
      } else {
        if ((r_o1_seq1start + r_o1_seq2start) > (r_o2_seq1start + r_o2_seq2start)) {
          r_ret := 1;
        } else {
          r_ret := 0;
        }
      }
    }
  }
  assert(l_ret == (-1 * r_ret));
 }
