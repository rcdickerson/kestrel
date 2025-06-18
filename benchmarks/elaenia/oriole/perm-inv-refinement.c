/* @ELAENIA
 * pre: (forall.list_in == exists.list_in)
     && (forall.length == exists.length)
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> lst_read(lst_store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> lst_read(lst_store(a, i, x), j) == lst_read(a, j));
 * pre_sketch: left.length <= 4;
 * forall: refinement;
 * exists: original;
 * post: forall.sum == exists.sum;
 * aspecs:
 *   sort(list) {
 *     pre:  true;
 *     post: (forall val: int :: lst_contains(list, val) == lst_contains(ret!, val))
          && (forall i: int, j: int :: i < j ==> lst_read(ret!, i) <= lst_read(ret!, j));
 *   }
 * especs:
 *   shuffle(list) {
 *     choiceVars: n;
 *     pre: forall val: int :: lst_contains(list, val) == lst_contains(n, val);
 *     post: ret! == n;
 *   }
 */

void _test_gen(int list, int length) {
  if (length < 0) { length = length * -1; }
  length = length % 5;
  _main(list, length, list, length);
}

int lst_contains(int list, int value);
int lst_read(int list, int index);
int lst_store(int list, int index, int value);

int shuffle(int list);
int sort(int list);

void original(int list_in, int length) {
  int list;
  list = shuffle(list_in);
  int sum = 0;
  int i = 0;
  while (i < length) {
    _invariant("l_sum == r_sum");
    _invariant("l_i == r_i");
    int val = lst_read(list, i);
    sum = sum + val;
    i = i + 1;
  }
}

void refinement(int list_in, int length) {
  int list;
  list = sort(list_in);
  int sum = 0;
  int i = 0;
  while (i < length) {
    int val = lst_read(list, i);
    sum = sum + val;
    i = i + 1;
  }
}
