/*
 * Based on http://codedbot.com/questions/5138521/comparison-method-violates-its-general-contract-overlapping-conditions
 *
 */

// #include "seahorn/seahorn.h"
// extern int arb_int(void);

int main() {

    int o1_score = arb_int();
    int o1_seq1start = arb_int();
    int o1_seq2start = arb_int();

    int o2_score = arb_int();
    int o2_seq1start = arb_int();
    int o2_seq2start = arb_int();

    rel_left();

    int ret_1;

    // first compare scores
    if (o1_score > o2_score) {
        ret_1 = -1; /* higher score for o1 -> o1 */
    }
    else if (o1_score < o2_score) {
        ret_1 = 1; /* higher score for o2 -> o2 */
    }

    // scores are equal, go on with the position
    else if ((o1_seq1start + o1_seq2start) < (o2_seq1start+o2_seq2start)) {
        ret_1 = -1; /* o1 is farther left */
    }
    else if ((o1_seq1start + o1_seq2start) > (o2_seq1start+o2_seq2start)) {
        ret_1 = 1; /* o2 is farther left */
    }
    else {
        // they're equally good
        ret_1 = 0;
    }

    rel_mid();

    int ret_2;

    // first compare scores
    if (o2_score > o1_score) {
        ret_2 = -1; /* higher score for o1 -> o1 */
    }
    else if (o2_score < o1_score) {
        ret_2 = 1; /* higher score for o2 -> o2 */
    }

    // scores are equal, go on with the position
    else if ((o2_seq1start + o2_seq2start) < (o1_seq1start+o1_seq2start)) {
        ret_2 = -1; /* o1 is farther left */
    }
    else if ((o2_seq1start + o2_seq2start) > (o1_seq1start+o1_seq2start)) {
        ret_2 = 1; /* o2 is farther left */
    }
    else {
        // they're equally good
        ret_2 = 0;
    }

    rel_right();

//    sassert(ret_2 == -ret_1);
}
