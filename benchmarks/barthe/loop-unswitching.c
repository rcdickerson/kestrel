/* @KESTREL
 * pre: k_1 == k_2 && x_1 == x_2 &&
        for _i in (0..N) { a_1[_i] == a_2[_i] && b_1[_i] == b_2[_i] && c_1[_i] == c_2[_i]};
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
int k_1;
int k_2;
int x_1;
int x_2;

void _generator(int _arr1[N], int _arr2[N], int _arr3[N], int _k, int _x) {
  int _ai = 0;
  while (_ai < N) {
    a_1[_ai] = _arr1[_ai];
    a_2[_ai] = _arr1[_ai];
    b_1[_ai] = _arr2[_ai];
    b_2[_ai] = _arr2[_ai];
    c_1[_ai] = _arr3[_ai];
    c_2[_ai] = _arr3[_ai];
    _ai = _ai + 1;
  }
  k_1 = _k;
  k_2 = _k;
  x_1 = _x;
  x_2 = _x;
}

void left(void) {
  int i = 0;
  while (i < N) {
    a_1[i] = a_1[i] + k_1;
    if (x_1 < 7) {
      b_1[i] = a_1[i] * c_1[i];
    } else {
      b_1[i] = a_1[i - 1] * b_1[i - 1];
    }
    i = i + 1;
  }
}

void right(void) {
  if (x_2 < 7) {
    int j = 0;
    while (j < N) {
      a_2[j] = a_2[j] + k_2;
      b_2[j] = a_2[j] * c_2[j];
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < N) {
      a_2[j] = a_2[j] + k_2;
      b_2[j] = a_2[j - 1] * b_2[j - 1];
      j = j + 1;
    }
  }
}
