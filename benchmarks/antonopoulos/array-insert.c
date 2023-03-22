extern int  arbitraryI(void);
extern int* arbitraryIP(void);
extern int  shiftArray(int* A, int idx, int amt);

extern void rel_left();
extern void rel_mid();
extern void rel_right();

void prog(int* A, int len, int h) {
  int i = 0;

  while( i < len && A[i] < h) {
    i = i + 1;
  }
  len = shiftArray(A, i, 1);
  A[i] = h;
  while (i < len) {
    i = i + 1;
  }
}

int main(void) {
  // Not quite right.

  int* A1  = arbitraryIP();
  int* A2  = arbitraryIP();
  // Assert A's are equal.

  int  len = arbitraryI();
  int  h   = arbitraryI();

  rel_left();
  prog(A1, len, h);
  rel_mid();
  prog(A2, len, h);
  rel_right();

  sassert(A1 == A2); // Need contents instead of addresses.
}
