/* @KESTREL
 * pre: forall i: int ::
     (read(l_list_in, i) >= read(r_list_in, i) || read(r_list_in, i) - read(l_list_in, i) < epsilon) &&
     (read(l_list_in, i) <  read(r_list_in, i) || read(l_list_in, i) - read(r_list_in, i) < epsilon);
 * left: sort;
 * right: sort;
 * post: forall j: int ::
     (read(l_list_in, j) >= read(r_list_in, j) || read(r_list_in, j) - read(l_list_in, j) < epsilon) &&
     (read(l_list_in, j) <  read(r_list_in, j) || read(l_list_in, j) - read(r_list_in, j) < epsilon);
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
