/* @KESTREL
 * pre: left.list_in == right.list_in
     && left.val == right.val;
 * left: sll_delete;
 * right: dll_delete;
 * post: left.list == right.list;
 */

// SLL interface.
int sll_val(int list);
int sll_next(int list);
int sll_set_next(int list, int next);
int sll_null(int list);

// DLL interface.
int dll_val(int list);
int dll_prev(int list);
int dll_set_prev(int list, int prev);
int dll_set_next(int list, int prev);
int dll_next(int list);
int dll_null(int list);


void sll_delete(int list_in, int val) {
  int h  = list_in;
  int p = list_in;
  while(sll_null(h) == 0) {
    if(sll_val(h) == val && h == list_in) {
      list_in = sll_next(list_in);
      break;
    } else if(sll_val(h) == val) {
      sll_set_next(sll_next(p), sll_next(h));
      break;
    } else {
      p = h;
      h = sll_next(h);
    }
  }
}

void dll_delete(int list_in, int val) {
  int h  = list_in;
  while(dll_null(h) == 0) {
    if(dll_val(h) == val && h == list_in) {
      list_in = dll_next(list_in);
      dll_set_prev(list_in, dll_prev(h));
      break;
    } else if(dll_val(h) == val) {
      int p = dll_prev(h);
      int n = dll_next(h);
      dll_set_next(p,n);
      if(dll_null(n) == 0) {
        dll_set_prev(n,p);
      }
      break;
    } else {
      h = dll_next(h);
    }
  }
}
