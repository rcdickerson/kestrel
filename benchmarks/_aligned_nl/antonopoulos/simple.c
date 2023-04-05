#include "seahorn/seahorn.h"

extern int arb_int();

int main() {
int N = arb_int();
int x1 = 0;
int x2 = 0;
int i1 = 0;
int i2 = 0;
while (i1 <= N && i2 <= N) {
x1 = x1 + 1;
i1 = i1 + 1;
x2 = x2 + 1;
i2 = i2 + 1;
};
while (i1 <= N) {
x1 = x1 + 1;
i1 = i1 + 1;
};
while (i2 <= N) {
x2 = x2 + 1;
i2 = i2 + 1;
}
sassert(x1 == x2);
}
