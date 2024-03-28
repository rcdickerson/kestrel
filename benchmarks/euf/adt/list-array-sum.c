/* @KESTREL
 * pre: (forall list: int :: r_advance(list, list, 0) == 1)
     && (forall l1: int, l2: int :: l1 != l2 ==> r_advance(l1, l2, 0) == 0)
     && (forall l1: int, l2: int, l2next: int, n: int ::
             (l2next == list_next(l2) && r_advance(l1, l2, n) == 1)
             ==> r_advance(l1, l2next, n + 1) == 1)
     && (forall list: int, n: int ::
             r_advance(left.list_in, list, n) == 1
              ==> list_val(list) == read(right.arr_in, n));
 * left: sum_list;
 * right: sum_array;
 * post: left.sum == right.sum;
 */

// List interface.
int list_val(int list);
int list_next(int list);
int list_null(int list);

// Array interface.
int read(int list_id, int index);
int store(int list_id, int index, int value);

// A relation indicating that list l2 corresponds to list l1 after n
// advancements.
int r_advance(int l1, int l2, int n);

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
