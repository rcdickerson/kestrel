/* @KESTREL
 * pre: for _i in (1..10) {
     (left.a[_i] >= right.a[_i] || right.a[_i] - left.a[_i] < epsilon) &&
     (left.a[_i] <  right.a[_i] || left.a[_i] - right.a[_i] < epsilon)
   };
 * left: left;
 * right: right;
 * post: for _j in (1..10) {
     (left.a[_j] >= right.a[_j] || right.a[_j] - left.a[_j] < epsilon) &&
     (left.a[_j] <  right.a[_j] || left.a[_j] - right.a[_j] < epsilon)
   };
 */

#define N 10

const float epsilon = 0.01;

void _generator(float _arr[N]) {
  int _ai = 0;
  float l_a[N];
  float r_a[N];
  while (_ai < N) {
    if (_ai % 2 == 0) {
      l_a[_ai] = _arr[_ai] + 0.001;
      r_a[_ai] = _arr[_ai];
    } else {
      l_a[_ai] = _arr[_ai];
      r_a[_ai] = _arr[_ai] + 0.001;
    }
    _ai = _ai + 1;
  }
}

void left(float a[N]) {
  int i = 0;
  while (i < N) {
    int j = N - 1;
    while (j > i) {
      if (a[j - 1] > a[j]) {
        float temp = a[j];
        a[j] = a[j - 1];
        a[j - 1] = temp;
      }
      j = j - 1;
    }
    i = i + 1;
  }
}

void right(float a[N]) {
  int i = 0;
  while (i < N) {
    int j = N - 1;
    while (j > i) {
      if (a[j - 1] > a[j]) {
        float temp = a[j];
        a[j] = a[j - 1];
        a[j - 1] = temp;
      }
      j = j - 1;
    }
    i = i + 1;
  }
}
