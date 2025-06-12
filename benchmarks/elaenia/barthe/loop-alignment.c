/* @ELAENIA
 * pre: left.size == right.size
     && left.size >= 1
     && left.a == right.a
     && left.b == right.b;
 * pre_sketch: left.size <= 4;
 * forall: left;
 * exists: right;
 * post: left.d == right.d;
 * aspecs:
 *   evenIndex(size) {
 *     pre: size >= 1;
 *     post: 0 <= ret! && ret! < size && ret! % 2 == 0;
 *   }
 * especs:
 *   anyIndex(size) {
 *     choiceVars: n;
 *     pre: size >= 1 && 0 <= n && n < size;
 *     post: ret! == n;
 *   }
 */

int evenIndex(int size);
int anyIndex(int size);

void _test_gen(int size,
               int a0, int a1, int a2, int a3,
               int b0, int b1, int b2, int b3) {
  if (size < 0) { size = size * -1; }
  size = size % 10;

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
    int idx;
    idx = evenIndex(size);
    b[i] = a[idx];
    d[i] = b[i-1];
    i = i + 1;
  }
}

void right(int size, int a[size+1], int b[size+1]) {
  int j = 1;
  int d[size+1] = {0};

  int first_idx;
  first_idx = anyIndex(size);
  d[1] = b[first_idx];
  while (j <= size - 1) {
    int idx;
    idx = anyIndex(size);
    b[j] = a[idx];
    d[j+1] = b[j];
    j = j + 1;
  }
  int final_idx;
  final_idx = anyIndex(size);
  b[size] = a[final_idx];
}
