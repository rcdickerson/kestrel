#include "seahorn/seahorn.h"

extern int havoc();

int main(void) {
  int x = havoc();

  int y_1 = 0;
  int z_1 = 2 * x;
  while (z_1 > 0) {
    z_1 = z_1 - 1;
    y_1 = y_1 + x;
  }

  int y_2 = 0;
  int z_2 = x;
  while (z_2 > 0) {
    z_2 = z_2 - 1;
    y_2 = y_2 + x;
  }
  y_2 = 2 * y_2;

  sassert(y_1 == y_2);
}
