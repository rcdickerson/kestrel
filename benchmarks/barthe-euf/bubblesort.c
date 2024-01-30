/* @KESTREL
 * pre: for p_i in (1..10) {
     (left.a[p_i] >= right.a[p_i] || right.a[p_i] - left.a[p_i] < epsilon) &&
     (left.a[p_i] <  right.a[p_i] || left.a[p_i] - right.a[p_i] < epsilon)
   };
 * left: sort;
 * right: sort;
 * post: for p_j in (1..10) {
     (left.a[p_j] >= right.a[p_j] || right.a[p_j] - left.a[p_j] < epsilon) &&
     (left.a[p_j] <  right.a[p_j] || left.a[p_j] - right.a[p_j] < epsilon)
   };
 */
// TODO: Specs should be universally quantified over list size.

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
