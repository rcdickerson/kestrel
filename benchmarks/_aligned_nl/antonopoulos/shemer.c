#include "seahorn/seahorn.h"

extern int arb_int();

int main() {
int x = arb_int();
int y1 = 0;
int y2 = 0;
int z1 = 2 * x;
int z2 = x;
while (z1 > 0 && z2 > 0) {
z1 = z1 - 1;
y1 = y1 + x;
z2 = z2 - 1;
y2 = y2 + x;
};
while (z1 > 0) {
z1 = z1 - 1;
y1 = y1 + x;
};
while (z2 > 0) {
z2 = z2 - 1;
y2 = y2 + x;
};
y2 = y2 * 2;
sassert(y1 == y2);
}
