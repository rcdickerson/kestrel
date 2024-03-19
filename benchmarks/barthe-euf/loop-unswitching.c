/* @KESTREL
 * pre: left.k_in == right.k_in
     && left.x_in == right.x_in
     && left.a_in == right.a_in
     && left.b_in == right.b_in
     && left.c_in == right.c_in;
 * left: left;
 * right: right;
 * post: (forall i: int :: (read(left.a, i) == read(right.a, i)))
      && (forall i: int :: (read(left.b, i) == read(right.b, i)))
      && (forall i: int :: (read(left.c, i) == read(right.c, i)));
 */

int read(int list_id, int index);
int store(int list_id, int index, int value);

void _generator(int _arr1, int _arr2, int _arr3, int _k, int _x, int _size) {
  int l_a_in = _arr1;
  int r_a_in = _arr1;
  int l_b_in = _arr1;
  int r_b_in = _arr1;
  int l_c_in = _arr1;
  int r_c_in = _arr1;
  int l_k_in = _k;
  int r_k_in = _k;
  int l_x_in = _x;
  int r_x_in = _x;
  int l_size = _size;
  int r_size = _size;
}


void _test_gen(int a, int b, int c, int k, int x, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(a, b, c, k, x, size, a, b, c, k, x, size);
}

void left(int a_in, int b_in, int c_in, int k_in, int x_in, int size) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int k = k_in;
  int x = x_in;

  int i = 0;
  while (i < size) {
    int read_ai = read(a, i);
    a = store(a, i, read_ai + k);
    if (x < 7) {
      int read_ai = read(a, i);
      int read_ci = read(c, i);
      b = store(b, i, read_ai * read_ci);
    } else {
      int read_ai_prev = read(a, i - 1);
      int read_bi_prev = read(b, i - 1);
      b = store(b, i, read_ai_prev  * read_bi_prev);
    }
    i = i + 1;
  }
}

void right(int a_in, int b_in, int c_in, int k_in, int x_in, int size) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int k = k_in;
  int x = x_in;

  if (x < 7) {
    int j = 0;
    while (j < size) {
      int read_aj = read(a, j);
      int read_cj = read(c, j);
      a = store(a, j, read_aj + k);
      b = store(b, j, read_aj * read_cj);
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < size) {
      int read_aj = read(a, j);
      int read_aj_prev = read(a, j - 1);
      int read_bj_prev = read(b, j - 1);
      a = store(a, j, read_aj + k);
      b = store(b, j, read_aj_prev * read_bj_prev);
      j = j + 1;
    }
  }
}
