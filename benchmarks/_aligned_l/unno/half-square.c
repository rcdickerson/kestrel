#include "seahorn/seahorn.h"
extern int arb_int(void);

int main(void) {

  int low = arb_int();

int h1 = arb_int();
assume(low > h1 && h1 > 0);
int i1 = 0;
int y1 = 0;
int v1 = 0;
while (h1 > i1) {
i1 = i1 + 1;
y1 = y1 + y1;
}
v1 = 1;
int h2 = arb_int();
assume(low > h2 && h2 > 0);
int i2 = 0;
int y2 = 0;
int v2 = 0;
while (low > i1 && h2 > i2) {
i1 = i1 + 1;
y1 = y1 + y1;
i2 = i2 + 1;
y2 = y2 + y2;
}
while (low > i1) {
i1 = i1 + 1;
y1 = y1 + y1;
}
while (h2 > i2) {
i2 = i2 + 1;
y2 = y2 + y2;
}
v2 = 1;
while (low > i2) {
i2 = i2 + 1;
y2 = y2 + y2;
}


  sassert(y1 == y2);
}