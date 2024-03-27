/* @KESTREL
 * pre: left.a_in == right.a_in
     && left.b_in == right.b_in
     && left.c_in == right.c_in
     && left.size_in == right.size_in
     && 2 <= left.size_in;
 * left: left;
 * right: right;
 * post: left.a == right.a
      && left.b == right.b
      && left.c == right.c;
 */

void _test_gen(int a, int b, int c, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(a, b, c, size, a, b, c, size);
}

int read(int list_id, int index);
int store(int list_id, int index, int value);

void left(int a_in, int b_in, int c_in, int size_in) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int size = size_in;

  int i = 0;
  while (i < size) {
    a = store(a, i, read(a, i) + 1);
    b = store(b, i, read(b, i) + read(a, i));
    c = store(c, i, read(c, i) + read(b, i));
    i = i + 1;
  }
}

void right(int a_in, int b_in, int c_in, int size_in) {
  int a = a_in;
  int b = b_in;
  int c = c_in;
  int size = size_in;

  int j = 0;
  a = store(a, 0, read(a, 0) + 1);
  b = store(b, 0, read(b, 0) + read(a, 0));
  a = store(a, 1, read(a, 1) + 1);

  while (j < size - 2) {
    a = store(a, j+2, read(a, j + 2) + 1);
    b = store(b, j+1, read(b, j + 1) + read(a, j + 1));
    c = store(c, j, read(c, j) + read(b, j));
    j = j + 1;
  }
  c = store(c, j,  read(c, j) + read(b, j));
  b = store(b, j + 1, read(b, j + 1) + read(a, j + 1));
  c = store(c, j + 1, read(c, j + 1) + read(b, j + 1));
}
