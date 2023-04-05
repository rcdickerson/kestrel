#include "seahorn/seahorn.h"
extern float havoc();

#define N 10
float a_1[N];
float a_2[N];

int main(void) {
  float epsilon = havoc();
  for(int i = 0; i < N; i++) {
    assume(a_2[i] <= a_1[i]);
    assume(a_1[i] - a_2[i] < epsilon);
  }

int i_1 = 0;
int i_2 = 0;
while (i_1 < N && i_2 < N) {
int j_1 = N - 1;
while (j_1 > i_1) {
if( a_1[j_1 - 1] > a_1[j_1] ) {
float temp = a_1[j_1];
a_1[j_1] = a_1[j_1 - 1];
a_1[j_1 - 1] = temp;
}
j_1 = j_1 - 1;
}
i_1 = i_1 + 1;
int j_2 = N - 1;
while (j_2 > i_2) {
if( a_2[j_2 - 1] > a_2[j_2] ) {
float temp = a_2[j_2];
a_2[j_2] = a_2[j_2 - 1];
a_2[j_2 - 1] = temp;
}
j_2 = j_2 - 1;
}
i_2 = i_2 + 1;
}
while (i_1 < N) {
int j_1 = N - 1;
while (j_1 > i_1) {
if( a_1[j_1 - 1] > a_1[j_1] ) {
float temp = a_1[j_1];
a_1[j_1] = a_1[j_1 - 1];
a_1[j_1 - 1] = temp;
}
j_1 = j_1 - 1;
}
i_1 = i_1 + 1;
}
while (i_2 < N) {
int j_2 = N - 1;
while (j_2 > i_2) {
if( a_2[j_2 - 1] > a_2[j_2] ) {
float temp = a_2[j_2];
a_2[j_2] = a_2[j_2 - 1];
a_2[j_2 - 1] = temp;
}
j_2 = j_2 - 1;
}
i_2 = i_2 + 1;
}

  for(int i = 0; i < N; i++) {
    sassert(a_2[i] <= a_1[i]);
    sassert(a_1[i] - a_2[i] < epsilon);
  }
}
