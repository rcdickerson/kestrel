void left(int B, int C, int N, int x) {
  int i = 0;
  int j = 0;
  while (i < N ) {
    j = i * B + C;
    x = x + j;
    i = i + 1;
  }
}
