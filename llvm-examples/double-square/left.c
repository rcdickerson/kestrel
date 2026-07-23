void _test_gen(int x) {
    x = x % 50; 
    _main(x, x);
}

void left(int x) {
  int z = 0;
  int y = 0;
  z = 2*x;
  while (z>0) {
    _invariant("l_y == r_y");
    _invariant("l_z == r_z");
    z = z - 1;
    y = y+x;
  }
}
