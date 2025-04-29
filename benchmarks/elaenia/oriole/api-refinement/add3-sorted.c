/* @ELAENIA
 * pre: (forall.list_in == exists.list_in)
     && (forall.length == exists.length)
     && (forall.length >= 0)
     && (forall.length <= 3)
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==> read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==> read(store(a, i, x), j) == read(a, j));
 * forall: refinement;
 * exists: original;
 * post: forall.list == exists.list;
 * aspecs:
 *   sort(list) {
 *     pre:  true;
 *     post: (forall val: int :: contains(list, val) == contains(ret!, val))
          && (forall i: int, j: int :: i < j ==> read(ret!, i) <= read(ret!, j));
 *   }
 * especs:
 *   shuffle(list) {
 *     choiceVars: n;
 *     pre: forall val: int :: contains(list, val) == contains(n, val);
 *     post: ret! == n;
 *   }
 */

void _test_gen(int list, int length) {
  if (length < 0) { length = length * -1; }
  length = length % 5;
  _main(list, length, list, length);
}

int contains(int list, int value);
int read(int list, int index);
int store(int list, int index, int value);

int shuffle(int list);
int sort(int list);

void original(int list_in, int length) {
  int list;
  list = shuffle(list_in);
  int i = 0;
  while (i < length) {
    int val_i = read(list, i);
    int updated = store(list, i, val_i + 3);
    list = updated;
    i = i + 1;
  }
}

void refinement(int list_in, int length) {
  int list;
  list = sort(list_in);
  int i = 0;
  while (i < length) {
    int val_i = read(list, i);
    int updated = store(list, i, val_i + 3);
    list = updated;
    i = i + 1;
  }
}
