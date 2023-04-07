#include "seahorn/seahorn.h"
extern int arb_int(void);

int main(void) {
  int x = arb_int();

int y1 = x;
int y2 = x;
int z2 = 16;
int z1 = 24;
int w1 = 0;
int w2 = 0;
while (y1 > 4 && y2 > 4) {
if( w1 % 2 == 0 ) {
z1 = z1 * y1;
y1 = y1 - 1;
}
w1 = w1 + 1;
if( w2 % 3 == 0 ) {
z2 = z2 * 2;
y2 = y2 - 1;
}
w2 = w2 + 1;
}
while (y1 > 4) {
if( w1 % 2 == 0 ) {
z1 = z1 * y1;
y1 = y1 - 1;
}
w1 = w1 + 1;
}
while (y2 > 4) {
if( w2 % 3 == 0 ) {
z2 = z2 * 2;
y2 = y2 - 1;
}
w2 = w2 + 1;
}

  sassert(z1 > z2);
}
