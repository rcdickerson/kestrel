/* @KESTREL
 * pre: for _i in (0..N) { a_1[_i] == a_2[_i] && b_1[_i] == b_2[_i] && c_1[_i] == c_2[_i] };
 * left: left;
 * right: right;
 * post: for _j in (0..N) { a_1[_j] == a_2[_j] && b_1[_j] == b_2[_j] && c_1[_j] == c_2[_j] };
 */

const int N = 10;
int a_1[N];
int b_1[N];
int c_1[N];
int a_2[N];
int b_2[N];
int c_2[N];

void left(void) {
  int i = 0;
  while (i < N ) {
    a_1[i] = a_1[i] + 1;
    b_1[i] = b_1[i] + a_1[i];
    c_1[i] = c_1[i] + b_1[i];
    i = i + 1;
  }
}

void right(void) {
  int j = 0;
  a_2[0] = a_2[0] + 1;
  b_2[0] = b_2[0] + a_2[0];
  a_2[1] = a_2[1] + 1;

  while (j < N - 2) {
    a_2[j+2] = a_2[j+2] + 1;
    b_2[j+1] = b_2[j+1] + a_2[j+1];
    c_2[j] = c_2[j] + b_2[j];
    j = j + 1;
  }
  c_2[j] = c_2[j] + b_2[j];
  b_2[j+1] = b_2[j+1] + a_2[j+1];
  c_2[j+1] = c_2[j+1] + b_2[j+1];
}
