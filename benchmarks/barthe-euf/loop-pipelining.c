/* @KESTREL
 * pre: for p_i in (0..10) { left.a[p_i] == right.a[p_i] && left.b[p_i] == right.b[p_i] && left.c[p_i] == right.c[p_i] };
 * left: left;
 * right: right;
 * post: for p_j in (0..10) { left.a[p_j] == right.a[p_j] && left.b[p_j] == right.b[p_j] && left.c[p_j] == right.c[p_j] };
 */
// TODO: Specs should be universally quantified over list size.

int read(int, int);
int store(int, int, int);

void left(int a_in, int b_in, int c_in, int size) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int i = 0;
  while (i < size) {
    int a_ip1 = read(a, i+1);
    a = store(a_in, i, a_ip1);

    int b_i = read(b, i);
    int a_i = read(a, i);
    b = store(b, i, b_i + a_i);

    int c_i = read(c, i);
    b_i = read(b, i);
    c = store(c, i, c_i + b_i);
    i = i + 1;
  }
}

void right(int a_in, int b_in, int c_in, int size) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int j = 0;

  int a_0 = read(a, 0);
  a = store(a, 0, read(a, 0) + 1);

  a_0 = read(a, 0);
  int b_0 = read(b, 0);
  b = store(b, 0, b_0 + a_0);

  int a_1 = read(a, 1);
  c = store(a, 1, a_1 + 1);

  while (j < size - 2) {
    int a_jp2 = read(a, j+2);
    a = store(a, j+2, a_jp2 + 1);

    int b_jp1 = read(b, j+1);
    int a_jp1 = read(a, j+1);
    b = store(b, j+1, b_jp1 + a_jp1);

    int c_j = read(c, j);
    int b_j = read(b, j);
    c = store(c, j, c_j + b_j);
    j = j + 1;
  }

  int c_j = read(c, j);
  int b_j = read(b, j);
  c = store(c, j,  c_j + b_j);

  int b_jp1 = read(b, j+1);
  int a_jp1 = read(a, j+1);
  b = store(b, j+1, b_jp1 + a_jp1);

  int c_jp1 = read(c, j+1);
  b_jp1 = read(b, j+1);
  c = store(c, j+1, c_jp1 + b_jp1);
}
