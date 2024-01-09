/* @KESTREL
 * pre: for _i in (1..10) {
     (left.a[_i] >= right.a[_i] || right.a[_i] - left.a[_i] < epsilon) &&
     (left.a[_i] <  right.a[_i] || left.a[_i] - right.a[_i] < epsilon)
   };
 * left: sort;
 * right: sort;
 * post: for _j in (1..10) {
     (left.a[_j] >= right.a[_j] || right.a[_j] - left.a[_j] < epsilon) &&
     (left.a[_j] <  right.a[_j] || left.a[_j] - right.a[_j] < epsilon)
   };
 */
// TODO: Specs should be universally quantified over list size.

const float epsilon = 0.01;

float read(int, int);
void store(int, int, float);

void sort(int list, int size) {
  int i = 0;
  while (i < size) {
    int j = size - 1;
    while (j > i) {
      float prev = read(list, j - 1);
      float cur  = read(list, j);
      if (prev > cur) {
        float temp = read(list, j);
        store(list, j, read(list, j-1));
        store(list, j - 1, temp);
      }
      j = j - 1;
    }
    i = i + 1;
  }
}
