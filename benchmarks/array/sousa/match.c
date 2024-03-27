/* @KESTREL
 * pre: left.o1_score == right.o2_score &&
        left.o1_seq1start == right.o2_seq1start &&
        left.o1_seq2start == right.o2_seq2start &&
        left.o2_score == right.o1_score &&
        left.o2_seq1start == right.o1_seq1start &&
        left.o2_seq2start == right.o1_seq2start;
 * left: cmp;
 * right: cmp;
 * post: left.ret == -1 * right.ret;
 */

/*
 * Based on http://codedbot.com/questions/5138521/comparison-method-violates-its-general-contract-overlapping-conditions
 */

void cmp(int o1_score, int o1_seq1start, int o1_seq2start,
         int o2_score, int o2_seq1start, int o2_seq2start) {
    int ret;

    // first compare scores
    if (o1_score > o2_score) {
        ret = -1; /* higher score for o1 -> o1 */
    }
    else if (o1_score < o2_score) {
        ret = 1; /* higher score for o2 -> o2 */
    }

    // scores are equal, go on with the position
    else if ((o1_seq1start + o1_seq2start) < (o2_seq1start+o2_seq2start)) {
        ret = -1; /* o1 is farther left */
    }
    else if ((o1_seq1start + o1_seq2start) > (o2_seq1start+o2_seq2start)) {
        ret = 1; /* o2 is farther left */
    }
    else {
        // they're equally good
        ret = 0;
    }
}
