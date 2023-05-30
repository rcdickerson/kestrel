/* @KESTREL
 * pre: for _i in (0..N) { a_1[_i] == a_2[_i] && b_1[0] == b_2[0] };
 * left: left;
 * right: right;
 * post: for _j in (1..N) { d_1[_j] == d_2[_j] };
 */

const int N = 20;
int a_1[N + 1];
int b_1[N + 1];
int d_1[N + 1];
int a_2[N + 1];
int b_2[N + 1];
int d_2[N + 1];

void left(void) {
  int i = 1;
  while (i <= N ) {
    b_1[i] = a_1[i];
    d_1[i] = b_1[i - 1];
    i = i + 1;
  }
}

void right(void) {
  int j = 1;
  d_2[1] = b_2[0];
  while (j <= N - 1) {
    b_2[j] = a_2[j];
    d_2[j+1] = b_2[j];
    j = j + 1;
  }
  b_2[N] = a_2[N];
}
