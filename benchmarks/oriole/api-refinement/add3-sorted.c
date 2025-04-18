/* @ELAENIA
 * pre: (forall i: int :: read(forall.a_in, i) == read(exists.a_in, i))
     && (forall i: int, j: int, a: int, x: int :: (i == j) ==>
         read(store(a, i, x), j) == x)
     && (forall i: int, j: int, a: int, x: int :: (i != j) ==>
         read(store(a, i, x), j) == read(a, j));
 * forall: refinement;
 * exists: original;
 * post: (forall i: int :: read(forall.a_in, i) == read(exists.a_in, i));
 * aspecs:
 *   sort(int list, int length) {
 *     pre:  true;
 *     post: (forall i: int :: read(ret!, i) <= read(ret!, i + 1));
 *   }
 * especs:
 *   shuffle(int list, int length) {
 *     choiceVars: n;
 *     pre: true;
 *     post: (forall i: int :: read(list, i) <= read(list, i + 1));
 *   }
 */

void _test_gen(int list, int length) {
  if (length < 0) { length = length * -1; }
  length = length % 10;
  _main(list, length, list, length);
}

int read(int list_id, int index);
int store(int list_id, int index, int value);
int shuffle(int list, int length);
int sort(int list, int length);

void original(int list, int length) {
  list = shuffle(list, length);
  int i = 0;
  while (i < length) {
    list = store(list, i, read(list, i) + 3);
  }
}

void refinement(int list, int length) {
  list = sort(list, length);
  int i = 0;
  while (i < length) {
    list = store(list, i, read(list, i) + 3);
  }
}
