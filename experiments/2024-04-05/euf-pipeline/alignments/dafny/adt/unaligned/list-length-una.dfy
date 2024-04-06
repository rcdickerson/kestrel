
function sll_val(list: int): int

function sll_next(list: int): int

function sll_null(list: int): int

function dll_val(list: int): int

function dll_prev(list: int): int

function dll_next(list: int): int

function dll_null(list: int): int

function r(sll: int, dll: int): int

method Main(l_lst_in: int, r_lst_in: int)
  decreases *
 {
  assume((r(l_lst_in, r_lst_in) == 1) && (forall sll: int, dll: int :: ((!(r(sll, dll) == 1)) || (r(sll_next(sll), dll_next(dll)) == 1)) && (forall sll: int, dll: int :: ((!(r(sll, dll) == 1)) || (sll_val(sll) == dll_val(dll))) && (forall sll: int, dll: int :: ((!(r(sll, dll) == 1)) || (sll_next(sll) == dll_next(dll))) && forall sll: int, dll: int :: ((!(r(sll, dll) == 1)) || (sll_null(sll) == dll_null(dll)))))));
  var l_lst: int := l_lst_in;
  var l_len: int := 0;
  if (sll_null(l_lst) == 0) {
    while (sll_null(l_lst) == 0) {
      l_len := (l_len + 1);
      l_lst := sll_next(l_lst);
    }
  }
  var r_lst: int := r_lst_in;
  var r_len: int := 0;
  if (dll_null(r_lst) == 0) {
    while (dll_null(r_lst) == 0) {
      r_len := (r_len + 1);
      r_lst := dll_next(r_lst);
    }
  }
  assert(l_len == r_len);
 }
