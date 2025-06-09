/* @ELAENIA
 * pre: left.size == right.size
     && left.size > 0
     && left.x == right.x
     && left.a == right.a
     && left.b == right.b
     && left.c == right.c;
 * pre_sketch: left.size <= 4;
 * forall: left;
 * exists: right;
 * post: left.a == right.a
      && left.b == right.b
      && left.c == right.c;
 * aspecs:
 *   randEven(max) {
 *     pre: true;
 *     post: 0 <= ret! && ret! < max && ret! % 2 == 0;
 *   }
 * especs:
 *   randB(max) {
 *     choiceVars: n;
 *     pre: 0 <= n && n < max;
 *     post: ret! == n;
 *   }
 */

int randEven(int max);
int randB(int max);

void _test_gen(int size, int x,
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

  _main(size, a, b, c, x, size, a, b, c, x);
}

void left(int size, int a[size], int b[size], int c[size], int x) {
  int i = 0;
  int k;
  while (i < size) {
    k = randEven(100);
    a[i] = a[i] + k;
    if (x < 7) {
      b[i] = a[i] * c[i];
    } else {
      b[i] = a[i-1] * b[i-1];
    }
    i = i + 1;
  }
}

void right(int size, int a[size], int b[size], int c[size], int x) {
  int k;
  if (x < 7) {
    int j = 0;
    while (j < size) {
      k = randB(100);
      a[j] = a[j] + k;
      b[j] = a[j] * c[j];
      j = j + 1;
    }
  } else {
    int j = 0;
    while (j < size) {
      k = randB(100);
      a[j] = a[j] + k;
      b[j] = a[j-1] * b[j-1];
      j = j + 1;
    }
  }
}
