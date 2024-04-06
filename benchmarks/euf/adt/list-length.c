/* @KESTREL
 * pre: r(left.lst_in, right.lst_in) == 1
     && (forall sll: int, dll: int :: r(sll, dll) == 1 ==> r(sll_next(sll), dll_next(dll)) == 1)
     && (forall sll: int, dll: int :: r(sll, dll) == 1 ==> sll_val(sll)  == dll_val(dll))
     && (forall sll: int, dll: int :: r(sll, dll) == 1 ==> sll_next(sll) == dll_next(dll))
     && (forall sll: int, dll: int :: r(sll, dll) == 1 ==> sll_null(sll) == dll_null(dll));
 * left: sll_length;
 * right: dll_length;
 * post: left.len == right.len;
 */

// Singly linked lists.
int sll_val(int list);
int sll_next(int list);
int sll_null(int list);

// Doubly linked lists.
int dll_val(int list);
int dll_prev(int list);
int dll_next(int list);
int dll_null(int list);

int r(int sll, int dll);

void _test_gen(int lst) {
  _main(lst, lst);
}

void sll_length(int lst_in) {
  int lst = lst_in;

  int len = 0;
  while(sll_null(lst) == 0) {
    _invariant("r(left.lst, right.lst) == 1");
    len = len + 1;
    lst = sll_next(lst);
  }
}

void dll_length(int lst_in) {
  int lst = lst_in;

  int len = 0;
  while(dll_null(lst) == 0) {
    len = len + 1;
    lst = dll_next(lst);
  }
}
