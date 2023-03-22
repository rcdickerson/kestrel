#include "seahorn/seahorn.h"
extern int arb_int(void);

int main() {
int o1_score = arb_int();
int o1_seq1start = arb_int();
int o1_seq2start = arb_int();
int o2_score = arb_int();
int o2_seq1start = arb_int();
int o2_seq2start = arb_int();
int ret_1;
int ret_2;
if( o1_score > o2_score ) {
ret_1 = -1;
} else {
if( o1_score < o2_score ) {
ret_1 = 1;
} else {
if( o1_seq1start + o1_seq2start < o2_seq1start + o2_seq2start ) {
ret_1 = -1;
} else {
if( o1_seq1start + o1_seq2start > o2_seq1start + o2_seq2start ) {
ret_1 = 1;
} else {
ret_1 = 0;
}
}
}
}
if( o2_score > o1_score ) {
ret_2 = -1;
} else {
if( o2_score < o1_score ) {
ret_2 = 1;
} else {
if( o2_seq1start + o2_seq2start < o1_seq1start + o1_seq2start ) {
ret_2 = -1;
} else {
if( o2_seq1start + o2_seq2start > o1_seq1start + o1_seq2start ) {
ret_2 = 1;
} else {
ret_2 = 0;
}
}
}
}
}
