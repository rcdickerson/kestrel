/* @KESTREL
 * pre: left.x == right.x;
 * left: add_one;
 * right: add_one;
 * post: left.ret_val == right.ret_val;
 */
int add_one(int x) {
  int ret_val = x + 1;
  return ret_val;
}