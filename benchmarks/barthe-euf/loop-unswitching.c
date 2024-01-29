/* @KESTREL
 * pre: left.k == right.k && left.x == right.x &&
        for p_i in (0..10) { left.a[p_i] == right.a[p_i] && left.b[p_i] == right.b[p_i] && left.c[p_i] == right.c[p_i]};
 * left: left;
 * right: right;
 * post: for p_j in (0..10) { left.a[p_j] == right.a[p_j] && left.b[p_j] == right.b[p_j] && left.c[p_j] == right.c[p_j] };
 */
// TODO: Specs should be universally quantified over list size.

int read(int, int);
int store(int, int, int);

void left(int a_in, int b_in, int c, int k, int x, int size) {
  int i = 0;
  int a = a_in;
  int b = b_in;
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

void right(int a_in, int b_in, int c, int k, int x, int size) {
  int a = a_in;
  int b = b_in;
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
