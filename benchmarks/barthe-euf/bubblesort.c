/* @KESTREL
 * pre: forall i: int ::
     (read(left.a, i) >= right.a[i] || right.a[i] - left.a[i] < epsilon) &&
     (left.a[i] <  right.a[i] || left.a[i] - right.a[i] < epsilon);
 * left: sort;
 * right: sort;
 * post: forall p_j: int ::
     (left.a[p_j] >= right.a[p_j] || right.a[p_j] - left.a[p_j] < epsilon) &&
     (left.a[p_j] <  right.a[p_j] || left.a[p_j] - right.a[p_j] < epsilon);
 */

const float epsilon = 0.01;

float read(int, int);
int store(int, int, float);

void sort(int list_in, int size) {
  int list = list_in;
  int i = 0;
  while (i < size) {
    int j = size - 1;
    while (j > i) {
      float prev = read(list, j - 1);
      float cur  = read(list, j);
      if (prev > cur) {
        float val = read(list, j);
        float prev_val = read(list, j-1);
        list = store(list, j, prev_val);
        list = store(list, j - 1, val);
      }
      j = j - 1;
    }
    i = i + 1;
  }
}
