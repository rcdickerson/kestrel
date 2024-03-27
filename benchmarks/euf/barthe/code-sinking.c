/* @KESTREL
 * pre: left.a_in == right.a_in;
 * left: left;
 * right: right;
 * post: left.a == right.a;
 */

int read(int list_id, int index);
int store(int list_id, int index, int value);

void _test_gen(int list_id, int size) {
  if (size < 0) { size = size * -1; }
  size = size % 100;
  _main(list_id, size, list_id, size);
}

void left(int a_in, int size) {
  int a = a_in;
  int max = read(a, 0);
  int maxi = 0;
  int i = 0;
  while (i < size) {
    if (max < read(a, i)) {
      max = read(a, i);
      maxi = i;
    }
    i = i + 1;
  }
  int t = read(a, size);
  a = store(a, size, max);
  a = store(a, maxi, t);
}

void right(int a_in, int size) {
  int a = a_in;
  int j = 0;
  int max;
  int maxi;
  while (j < size) {
    if (j == 0) {
      max = read(a, 0);
      maxi = 0;
    }
    if (max < read(a, j)) {
      max = read(a, j);
      maxi = j;
    }
    if (j == size) {
      int t = read(a, size);
      a = store(a, size, max);
      a = store(a, maxi, t);
    }
    j = j + 1;
  }
}
