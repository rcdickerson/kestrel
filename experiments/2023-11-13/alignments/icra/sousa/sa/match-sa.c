#include "assert.h"

void main() {
  int l_o1_score = nondet();
  int l_o1_seq1start = nondet();
  int l_o1_seq2start = nondet();
  int l_o2_score = nondet();
  int l_o2_seq1start = nondet();
  int l_o2_seq2start = nondet();
  int r_o1_score = nondet();
  int r_o1_seq1start = nondet();
  int r_o1_seq2start = nondet();
  int r_o2_score = nondet();
  int r_o2_seq1start = nondet();
  int r_o2_seq2start = nondet();
  __VERIFIER_assume((l_o1_score == r_o2_score) && ((l_o1_seq1start == r_o2_seq1start) && ((l_o1_seq2start == r_o2_seq2start) && ((l_o2_score == r_o1_score) && ((l_o2_seq1start == r_o1_seq1start) && (l_o2_seq2start == r_o1_seq2start))))));
  int l_ret;
  if (l_o1_score > l_o2_score) {
    l_ret = (-1);
  } else {if (l_o1_score < l_o2_score) {
      l_ret = 1;
    } else {if ((l_o1_seq1start + l_o1_seq2start) < (l_o2_seq1start + l_o2_seq2start)) {
        l_ret = (-1);
      } else {if ((l_o1_seq1start + l_o1_seq2start) > (l_o2_seq1start + l_o2_seq2start)) {
          l_ret = 1;
        } else {l_ret = 0;
        }
      }
    }
  }
  int r_ret;
  if (r_o1_score > r_o2_score) {
    r_ret = (-1);
  } else {if (r_o1_score < r_o2_score) {
      r_ret = 1;
    } else {if ((r_o1_seq1start + r_o1_seq2start) < (r_o2_seq1start + r_o2_seq2start)) {
        r_ret = (-1);
      } else {if ((r_o1_seq1start + r_o1_seq2start) > (r_o2_seq1start + r_o2_seq2start)) {
          r_ret = 1;
        } else {r_ret = 0;
        }
      }
    }
  }
  __VERIFIER_assert(l_ret == (-1 * r_ret));
 }
