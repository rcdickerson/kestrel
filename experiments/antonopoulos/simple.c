//extern int arb_int(void);

//extern void rel_left();
//extern void rel_mid();
//extern void rel_right();

int prog(int N) {
  int x = 0;
  int i = 0;

  while( i <= N ) {
    x = x + 1;
    i = i + 1;
  }
  return x;
}


int main(void) {
  int N = arb_int();

  rel_left();
  int x1 = prog(N);
  rel_mid();
  int x2 = prog(N);
  rel_right();

  sassert(x1 == x2);
}
