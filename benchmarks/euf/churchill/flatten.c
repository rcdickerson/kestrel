/* @KESTREL
 * pre:   left.n_in == right.n_in &&
          left.m_in == right.m_in &&
          l_m_in >= 0;
 * left:  left;
 * right: right;
 * post:  left.k == right.k;
 */

void _test_gen(int n, int m) {
  if (n < 0) n = n * - 1;
  if (m < 0) m = m * - 1;
  n = n % 100;
  m = m % 100;
  _main(n, m, n, m);
}

int left(int n_in, int m_in) {
  int n = n_in;
  int m = m_in;

  int k = 0;
  int i = 0;
  while (i < n) {
    _invariant("left.k == right.k");
    int j = 0;
    while(j < m){
      _invariant("left.k == right.k + left.j");
      _invariant("left.j <= left.m");
      k = k + 1;
      j = j + 1;
   }
   i = i + 1;
  }
}

int right(int n_in, int m_in) {
  int n = n_in;
  int m = m_in;

  int k = 0;
  int i = 0;
  while(i<n){
    k = k + m;
    i = i + 1;
  }
}
