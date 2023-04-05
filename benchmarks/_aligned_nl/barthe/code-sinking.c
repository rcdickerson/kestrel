#include "seahorn/seahorn.h"

#define N 10
int a_1[N + 1];
int a_2[N + 1];

int main(void) {

  for (int i = 0; i < N; i++) assume(a_1[i] == a_2[i]);

int max_1 = a_1[0];
int maxi_1 = 0;
int i_1 = 0;
int j_2 = 0;
while (i_1 <= N) {
if( max_1 < a_1[i_1] ) {
max_1 = a_1[i_1];
maxi_1 = i_1;
}
i_1 = i_1 + 1;
}
int t_1 = a_1[N];
a_1[N] = max_1;
a_1[maxi_1] = t_1;
while (j_2 <= N) {
int max_2;
int maxi_2;
if( j_2 == 0 ) {
max_2 = a_2[0];
maxi_2 = 0;
}
if( max_2 < a_2[j_2] ) {
max_2 = a_2[j_2];
maxi_2 = j_2;
}
if( j_2 == N ) {
int t_2 = a_2[N];
a_2[N] = max_2;
a_2[maxi_2] = t_2;
}
j_2 = j_2 + 1;
}

  for (int i = 0; i < N; i++) sassert(a_1[i] == a_2[i]);
}
