extern int arb_int(void);

int main(void) {
  int N = arb_int();

  rel_left();

  int x1 = 0;
  int i1 = 0;

  while( i1 <= N ) {
    x1 = x1 + 1;
    i1 = i1 + 1;
  }

  rel_mid();

  int x2 = 0;
  int i2 = 0;

  while( i2 <= N ) {
    x2 = x2 + 1;
    i2 = i2 + 1;
  }

  rel_right();

  sassert(x1 == x2);
}
