/* @KESTREL
 * pre: left.lst_in == right.lst_in
     && left.target == right.target
     && (forall head:int, lst:int :: list_next(list_cons(head, lst)) == lst);
 * left: cons_and_find;
 * right: cons_and_find;
 * post: left.found_at == right.found_at;
 */

int list_val(int list);
int list_next(int list);
int list_cons(int head, int list);
int list_null(int list);

void _test_gen(int list, int target, int secret1, int secret2) {
  _main(list, target, secret1, list, target, secret2);
}
int _list_null(int list) {
  if (list % 5 == 0) {
    return 1;
  } else {
    return 0;
  }
}

void cons_and_find(int lst_in, int target, int h_secret_in) {
  int lst = lst_in;
  int h_secret = h_secret_in;

  lst = list_cons(h_secret, lst);
  lst = list_next(lst);
  int found_at = -1;
  int i = 0;
  while (list_null(lst) == 0) {
    _invariant("left.found_at == right.found_at");
    _invariant("left.i == right.i");
    _invariant("left.lst == right.lst");
    _invariant("left.target == right.target");
    i = i + 1;
    lst = list_next(lst);
    if (list_null(lst) == 0 && list_val(lst) == target) {
      found_at = i;
    }
  }
}
