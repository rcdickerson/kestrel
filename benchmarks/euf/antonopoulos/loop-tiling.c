/* @KESTREL
 * pre: left.a_in == right.a_in
     && left.n_in == right.n_in
     && left.m_in == right.m_in;
 * left:  left;
 * right: right;
 * post:  forall i: int, j: int ::
          read(left.a, (i * left.m) + j) == read(read(right.a, i), j);
 */

int read(int arr, int index);
int store(int arr, int index, int value);
int f(int);

void _test_gen(int a_left, int a_right, int m, int n) {
  if (m < 0) { m = m * -1; }
  if (n < 0) { n = n * -1; }
  m = m % 10;
  n = n % 10;
  _main(a_left, n, m, a_right, n, m);
}

void left(int a_in, int n_in, int m_in) {
  int a = a_in;
  int n = n_in;
  int m = m_in;
  int x = 0;
  while (x < n * m) {
    a = store(a, x, f(x));
    x = x + 1;
  }
}

void right(int a_in, int n_in, int m_in) {
  int a = a_in;
  int n = n_in;
  int m = m_in;
  int i = 0;
  while (i < n) {
    int j = 0;
    while (j < m) {
      a = store(a, i, store(read(a, i), j, f(i*n+j)));
      j = j + 1;
    }
    i = i + 1;
  }
}
