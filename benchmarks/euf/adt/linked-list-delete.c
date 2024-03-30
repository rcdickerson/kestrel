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
int sll_null(int list);

// DLL interface.
int dll_val(int list);
int dll_prev(int list);
int dll_next(int list);
int dll_null(int list);


void sll_delete(int list_in, int val) {
  int list = list_in;
  if(sll_null(list) == 0 && sll_val(list) == val) {
    list = sll_next(list);
  } else if(sll_null(list) == 0) {
    int h = sll_next(list);
    int p = list;
    while(sll_null(h) == 0) {
      if(sll_val(h) == val) {
        p = sll_next(h);
        break;
      } else {
        p = h;
        h = sll_next(h);
      }
    }
  }
}

void dll_delete(int list_in, int val) {
  int list = list_in;
  if(dll_null(list) == 0 && dll_val(list) == val) {
    list = dll_next(list);
  } else if(dll_null(list) == 0) {
    // List is not empty.
    int h = dll_next(list);
    while(dll_null(h) == 0) {
      if(dll_val(h) == val) {
        int p = dll_prev(h);
        int n = dll_next(h);
        int temp = p;
        p = n;
        if(dll_null(n) == 0) {
          n = temp;
        }
        break;
      } else {
        h = dll_next(h);
      }
    }
  }
}
