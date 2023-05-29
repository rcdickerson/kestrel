/* @KESTREL
 * pre: for i in (0..N) { a_1[i] == a_2[i] };
 * left: left;
 * right: right;
 * post: for i in (0..N) { a_1[i] == a_2[i] };
 */

const int N = 10;
int a_1[N + 1];
int a_2[N + 1];

void left(void) {
  int max = a_1[0];
  int maxi = 0;
  int i = 0;
  while (i <= N) {
    if (max < a_1[i]) {
      max = a_1[i];
      maxi = i;
    }
    i = i + 1;
  }
  int t = a_1[N];
  a_1[N] = max;
  a_1[maxi] = t;
}

void right(void) {
  int j = 0;
  while (j <= N) {
    int max;
    int maxi;
    if (j == 0) {
      max = a_2[0];
      maxi = 0;
    }
    if (max < a_2[j]) {
      max = a_2[j];
      maxi = j;
    }
    if (j == N) {
      int t = a_2[N];
      a_2[N] = max;
      a_2[maxi] = t;
    }
    j = j + 1;
  }
}
