/* @KESTREL
 * pre: list_val(left.list_in) == read(right.arr_in, 0);
 * left: sum_list;
 * right: sum_array;
 * post: left.sum <= right.sum;
 */

// List interface.
int list_val(int list);
int list_next(int list);
int list_null(int list);

// Array interface.
int read(int list_id, int index);
int store(int list_id, int index, int value);

void _test_gen(int arr, int list, int length) {
  if (length < 0) { length = length * -1; }
  length = length % 100;
  _main(list, length, arr, length);
}

void sum_list(int list_in, int length)
{
  int sum = 0;
  int list = list_in;
  int i = 0;
  while(i < length) {
    sum = sum + list_val(list);
    list = list_next(list);
    i = i + 1;
  }
}


void sum_array(int arr_in, int length)
{
  int sum = 0;
  int i = 0;
  while(i < length) {
    sum = sum + read(arr_in, i);
    i = i + 1;
  }
}
