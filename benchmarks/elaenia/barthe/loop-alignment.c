/* @ELAENIA
 * pre: left.size == right.size
     && left.size >= 1
     && left.a == right.a
     && left.b == right.b;
 * pre_sketch: left.size <= 4;
 * forall: left;
 * exists: right;
 * post: left.d == right.d;
 */

void _test_gen(int size,
               int a0, int a1, int a2, int a3,
               int b0, int b1, int b2, int b3) {
  if (size < 0) { size = size * -1; }
  size = size % 100;

  int a[size+1] = {0};
  if (size > 0) { a[0] = a0; }
  if (size > 1) { a[1] = a1; }
  if (size > 2) { a[2] = a2; }
  if (size > 3) { a[3] = a3; }

  int b[size+1] = {0};
  if (size > 0) { b[0] = b0; }
  if (size > 1) { b[1] = b1; }
  if (size > 2) { b[2] = b2; }
  if (size > 3) { b[3] = b3; }

  _main(size, a, b, size, a, b);
}

void left(int size, int a[size+1], int b[size+1]) {
  int i = 1;
  int d[size+1] = {0};
  while (i <= size) {
    b[i] = a[i];
    d[i] = b[i-1];
    i = i + 1;
  }
}

void right(int size, int a[size+1], int b[size+1]) {
  int j = 1;
  int d[size+1] = {0};
  d[1] = b[0];
  while (j <= size - 1) {
    b[j] = a[j];
    d[j+1] = b[j];
    j = j + 1;
  }
  b[size] = a[size];
}
