/* @KESTREL
 * pre: for i in (1..N) {
     (a_1[i] >= a_2[i] && a_1[i] - a_2[i] < epsilon) ||
     (a_2[i] >= a_1[i] && a_2[i] - a_1[i] < epsilon)
   };
 * left: bubble_sort;
 * right: bubble_sort;
 * post: for i in (1..N) {
     (a_1[i] >= a_2[i] && a_1[i] - a_2[i] < epsilon) ||
     (a_2[i] >= a_1[i] && a_2[i] - a_1[i] < epsilon)
   };
 */

const int N = 10;
float a_1[N];
float a_2[N];

const float epsilon = 4.0;

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
