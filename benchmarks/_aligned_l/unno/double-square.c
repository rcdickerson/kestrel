#include "seahorn/seahorn.h"
extern int arb_int(void);

int main() {
  int x = arb_int();

int h_1 = arb_int();
int x_1 = x;
int z_1 = 0;
int h_2 = arb_int();
int x_2 = x;
int y_1 = 0;
if( h_1 ) {
z_1 = 2 * x_1;
} else {
z_1 = x_1;
}
while (z_1 > 0) {
z_1 = z_1 - 1;
y_1 = y_1 + x_1;
}
if( !h_1 ) {
y_1 = 2 * y_1;
}
int z_2 = 0;
int y_2 = 0;
if( h_2 ) {
z_2 = 2 * x_2;
} else {
z_2 = x_2;
}
while (z_2 > 0) {
z_2 = z_2 - 1;
y_2 = y_2 + x_2;
}
if( !h_2 ) {
y_2 = 2 * y_2;
}

  sassert(y_1 == y_2);
}
