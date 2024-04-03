/* @KESTREL
 * pre: (forall key: int :: getValue(left.map_in, key) == read(right.list_in, key))
     && (forall i: int, j: int, m: int, x: int :: (i == j) ==> getValue(updateMap(m, i, x), j) == x)
     && (forall i: int, j: int, m: int, x: int :: (i != j) ==> getValue(updateMap(m, i, x), j) == getValue(m, j))
     && (forall i: int, j: int, l: int, x: int :: (i == j) ==> read(store(l, i, x), j) == x)
     && (forall i: int, j: int, l: int, x: int :: (i != j) ==> read(store(l, i, x), j) == read(l, j));
 * left: kv_update;
 * right: list_update;
 * post: forall key: int :: getValue(left.map, key) == read(right.list, key);
 */

// Key-Value Store interface.
int getValue(int kv_store, int key);
int updateMap(int kv_store, int key, int value);

// List interface.
int read(int list, int index);
int store(int list, int index, int value);

void kv_update(int map_in, int k, int v) {
  int map = map_in;
  map = updateMap(map, k, v);
}

void list_update(int list_in, int k, int v) {
  int list = list_in;
  list = store(list, k, v);
}
