/* @ELAENIA
 * pre: forall.list[0] == exists.list[0]
     && forall.list[1] == exists.list[1]
     && forall.list[2] == exists.list[2];
 * forall: refinement;
 * exists: original;
 * post: forall.list[0] == exists.list[0]
      && forall.list[1] == exists.list[1]
      && forall.list[2] == exists.list[2];
 * aspecs:
 *   sort(list[3]) {
 *     pre:  true;
 *     post: ret![0] <= ret![1] && ret![1] <= ret![2]
         && ( (ret![0] == list[0] && ret![1] == list[1] && ret![2] == list[2])
           || (ret![0] == list[0] && ret![1] == list[2] && ret![2] == list[1])
           || (ret![0] == list[1] && ret![1] == list[0] && ret![2] == list[2])
           || (ret![0] == list[1] && ret![1] == list[2] && ret![2] == list[0])
           || (ret![0] == list[2] && ret![1] == list[0] && ret![2] == list[1])
           || (ret![0] == list[2] && ret![1] == list[1] && ret![2] == list[0]));
 *   }
 * especs:
 *   shuffle(int list[3]) {
 *     choiceVars: n0, n1, n2;
 *     pre: (n0 == list[0] && n1 == list[1] && n2 == list[2])
         || (n0 == list[0] && n1 == list[2] && n2 == list[1])
         || (n0 == list[1] && n1 == list[0] && n2 == list[2])
         || (n0 == list[1] && n1 == list[2] && n2 == list[0])
         || (n0 == list[2] && n1 == list[0] && n2 == list[1])
         || (n0 == list[2] && n1 == list[1] && n2 == list[0]);
 *     post: ret![0] == n0 && ret![1] == n1 && ret![2] == n2;
 *   }
 */

void _test_gen(int a1, int a2, int a3) {
  int list1[3] = {a1, a2, a3};
  int list2[3] = {a1, a2, a3};
  _main(list1, list2);
}

int[3] shuffle(int list[3]);
int[3] sort(int list[3]);

void original(int list[3]) {
  shuffle(list);
  int i = 0;
  while (i < 3) {
    list[i] = list[i] + 3;
    i = i + 1;
  }
}

void refinement(int list[3]) {
  sort(list);
  int i = 0;
  while (i < 3) {
    list[i] = list[i] + 3;
    i = i + 1;
  }
}
