/* @KESTREL
 * pre: for _i in (1..N) {
     (a_1[_i] >= a_2[_i] && a_1[_i] - a_2[_i] < epsilon) ||
     (a_2[_i] >= a_1[_i] && a_2[_i] - a_1[_i] < epsilon)
   };
 * left: bubble_sort;
 * right: bubble_sort;
 * post: for _j in (1..N) {
     (a_1[_j] >= a_2[_j] && a_1[_j] - a_2[_j] < epsilon) ||
     (a_2[_j] >= a_1[_j] && a_2[_j] - a_1[_j] < epsilon)
   };
 */

const int N = 10;
float a_1[N];
float a_2[N];

const float epsilon = 0.01;

void _generator(float _arr[N]) {
  int _ai = 0;
  while (_ai < N) {
    if (_ai % 2 == 0) {
      a_1[_ai] = _arr[_ai] + 0.001;
      a_2[_ai] = _arr[_ai];
    } else {
      a_1[_ai] = _arr[_ai];
      a_2[_ai] = _arr[_ai] + 0.001;
    }
    _ai = _ai + 1;
  }
}

void bubble_sort(void) {
  int i = 0;
  while (i < N) {
    int j = N - 1;
    while (j > i) {
      if (a_1[j - 1] > a_1[j]) {
        float temp = a_1[j];
        a_1[j] = a_1[j - 1];
        a_1[j - 1] = temp;
      }
      j = j - 1;
    }
    i = i + 1;
  }
}
