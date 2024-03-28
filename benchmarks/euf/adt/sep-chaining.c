/* @KESTREL
 * pre: true;
 * left: linear_probe;
 * right: separate_chaining;
 * post: left.found == right.found;
 */

// List interface.
int list_read(int list_id, int index);
int list_val(int list);
int list_next(int list);
int list_null(int list);

//array representation
int read(int list_id, int index);
int store(int list_id, int index, int value);

int hash_ind(int value);

// Search the value val in a with hashing
void linear_probe(int arr_in, int val, int length) {
  int arr = arr_in;
    int index = hash_ind(val);
    int found = 0;
    int ind = index;
    if(read(arr,ind) == val) {
      found = 1;
    } else {
      ind = (ind + 1) % length;
      while(read(arr,ind) != val && ind != index) {
        ind = (ind + 1) % length;
      }
      if(read(arr,ind) == val) {
        found = 1;
      }
    }
}

void separate_chaining(int lst_in, int val) {
  int lst = lst_in;
  int index = hash_ind(val);
  int found = 0;
  lst = list_read(lst, index);
  while(list_null(lst) != 0) {
    if(list_val(lst) == val) {
      found = 1;
      break;
    }
    lst = list_next(lst);
  }
}
