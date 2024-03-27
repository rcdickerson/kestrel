/* @KESTREL
 * pre: (forall i: int :: f(g(i)) == g(f(i)))
     && left.n == right.n;
 * left: left;
 * right: right;
 * post: left.sum == right.sum;
 */

int f(int x);
int g(int x);

void _test_gen(int n) {
  if (n < 0) { n = n * -1; }
  n = n % 100;
  _main(n, n);
}

void left(int n) {
  int sum = 0;
  int i = 0;
  while (i < n) {
    int result = f(i);
    result = g(result);
    sum = sum + result;
    i = i + 1;
  }
}

void right(int n) {
  int sum = 0;
  int i = 0;
  while (i < n) {
    int result = g(i);
    result = f(result);
    sum = sum + result;
    i = i + 1;
  }
}
