/* @KESTREL
 * pre:   left.n == right.n;
 * left:  fib;
 * right: fib;
 * post:  left.f1 == right.f1;
 */

void _generator(int n) {
  int l_n = n;
  int r_n = n;
}


void fib(int n, int high) {
    int f1 = 1;
    int f2 = 0;
    int temp = 0;
    if (high) {
        while(n > 0) { f1 = f1 + f2; f2 = f1 - f2; n = n-1; }
    } else {
        while(n > 0) { temp = f2; f2 = f1; f1 = f2 + temp; n = n-1; }
    }
}
