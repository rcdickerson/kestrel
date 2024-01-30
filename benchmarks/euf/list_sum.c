/* @KESTREL
 * pre: true;
 * left: sum;
 * right: sum;
 * post: true;
 */

float read(int, int);
int store(int, int, float);

void sum(int list, int size) {
  int sum = 0;
  int i = 0;
  while (i < size) {
    sum = sum + read(list, i);
    i = i + 1;
  }
}
