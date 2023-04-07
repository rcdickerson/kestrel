#include "seahorn/seahorn.h"

extern int arb_int();

int main(void) {

int a = arb_int();
int b = arb_int();
int a1 = a;
int a2 = a;
int b1 = b;
int b2 = b;
int c1 = 0;
int c2 = 0;
while (a1 < b1 && a2 < b2) {
c1 = c1 + a1 * a1;
a1 = a1 + 1;
c2 = c2 + a2 * a2;
a2 = a2 + 1;
}
while (a1 < b1) {
c1 = c1 + a1 * a1;
a1 = a1 + 1;
}
while (a2 < b2) {
c2 = c2 + a2 * a2;
a2 = a2 + 1;
}

  sassert(c1 == c2);
}
