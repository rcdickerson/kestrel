/* @KESTREL
 * pre: for i in (0..N) { a_1[i] == a_2[i] && b_1[i] == b_2[i] && c_1[i] == c_2[i]
                          && left.k == right.k && left.x == right.x };
 * left: left;
 * right: right;
 * post: for i in (0..N) { a_1[i] == a_2[i] && b_1[i] == b_2[i] && c_1[i] == c_2[i] };
 */

const int N = 10;
int a_1[N];
int b_1[N];
int c_1[N];
int a_2[N];
int b_2[N];
int c_2[N];

void left(int k, int x) {
  int i = 0;
  while (i < N) {
    a_1[i] = a_1[i] + k;
    if (x < 7) {
      b_1[i] = a_1[i] * c_1[i];
    } else {
      b_1[i] = a_1[i - 1] * b_1[i - 1];
    }
    i = i + 1;
  }
}

void right(int k, int x) {
  if (x < 7) {
    int j = 0;
    while (j < N) {
      a_2[j] = a_2[j] + k;
      b_2[j] = a_2[j] * c_2[j];
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < N) {
      a_2[j] = a_2[j] + k;
      b_2[j] = a_2[j - 1] * b_2[j - 1];
      j = j + 1;
    }
  }
}
