/* @KESTREL
 * pre: forall i: int :: left.a[i] == right.a[i];
 * left: left;
 * right: right;
 * post: forall j: int :: left.a[j] == right.a[j];
 */

int read(int, int);
int store(int, int, int);

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
