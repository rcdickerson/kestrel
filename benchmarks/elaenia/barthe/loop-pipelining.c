/* @ELAENIA
 * pre: left.size == right.size
     && 2 <= left.size
     && left.a == right.a
     && left.b == right.b
     && left.c == right.c;
 * pre_sketch: left.size <= 4;
 * forall: left;
 * exists: right;
 * post: left.a == right.a && left.b == right.b && left.c == right.c;
 */

void _test_gen(int size,
               int a0, int a1, int a2, int a3,
               int b0, int b1, int b2, int b3,
               int c0, int c1, int c2, int c3) {
  if (size < 0) { size = size * -1; }
  size = size % 100;

  int a[size] = {0};
  if (size > 0) { a[0] = a0; }
  if (size > 1) { a[1] = a1; }
  if (size > 2) { a[2] = a2; }
  if (size > 3) { a[3] = a3; }

  int b[size] = {0};
  if (size > 0) { b[0] = b0; }
  if (size > 1) { b[1] = b1; }
  if (size > 2) { b[2] = b2; }
  if (size > 3) { b[3] = b3; }

  int c[size] = {0};
  if (size > 0) { c[0] = c0; }
  if (size > 1) { c[1] = c1; }
  if (size > 2) { c[2] = c2; }
  if (size > 3) { c[3] = c3; }

  _main(a, b, c, size, a, b, c, size);
}

void left(int size, int a[size], int b[size], int c[size]) {
  int i = 0;
  while (i < size) {
    a[i] = a[i] + 1;
    b[i] = b[i] + a[i];
    c[i] = c[i] + b[i];
    i = i + 1;
  }
}

void right(int size, int a[size], int b[size], int c[size]) {
  int j = 0;
  a[0] = a[0] + 1;
  b[0] = b[0] + a[0];
  a[1] = a[1] + 1;
  while (j < size - 2) {
    a[j+2] = a[j+2] + 1;
    b[j+1] = b[j+1] + a[j+1];
    c[j] = c[j] + b[j];
    j = j + 1;
  }
  c[j] = c[j] + b[j];
  b[j+1] = b[j+1] + a[j+1];
  c[j+1] = c[j+1] + b[j+1];
}
