#include "seahorn/seahorn.h"

#define N 10
int a_1[N + 1];
int b_1[N + 1];
int d_1[N + 1];
int a_2[N + 1];
int b_2[N + 1];
int d_2[N + 1];

int main() {
int i = 1;
int j = 1;
d_2[1] = b_2[0];
while (i <= N && j <= N - 1) {
b_1[i] = a_1[i];
d_1[i] = b_1[i - 1];
i = i + 1;
b_2[j] = a_2[j];
d_2[j + 1] = b_2[j];
j = j + 1;
}
while (i <= N) {
b_1[i] = a_1[i];
d_1[i] = b_1[i - 1];
i = i + 1;
}
while (j <= N - 1) {
b_2[j] = a_2[j];
d_2[j + 1] = b_2[j];
j = j + 1;
}
b_2[N] = a_2[N];

for (int i = 0; i <= N; i++) sassert(a_1[i] == a_2[i]);
for (int i = 0; i <= N; i++) sassert(b_1[i] == b_2[i]);
for (int i = 0; i <= N; i++) sassert(d_1[i] == d_2[i]);
}
