/* @KESTREL
 * pre: left.k == right.k && left.x == right.x &&
        forall i: int :: read(left.a_in, i) == read(right.a_in, i) && read(left.b_in, i) == read(right.b_in, i) && read(left.c_in, i) == read(right.c_in, i);
 * left: left;
 * right: right;
 * post: forall j: int :: read(left.a, j) == read(right.a, j) && read(left.b, j) == read(right.b, j) && read(left.c, j) == read(right.c, j);
 */

int read(int, int);
int store(int, int, int);

void _test_gen(int a, int b, int c, int k, int x, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(a, b, c, k, x, size, a, b, c, k, x, size);
}

void left(int a_in, int b_in, int c_in, int k, int x, int size) {
  int i = 0;
  int a = a_in;
  int b = b_in;
  int c = c_in;
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

void right(int a_in, int b_in, int c_in, int k, int x, int size) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
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
