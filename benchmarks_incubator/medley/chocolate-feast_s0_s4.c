/* @KESTREL
 * pre: 2 <= right._param_1 &&
        right._param_1 <= 100000 &&
        1 <= right._param_2 &&
        right._param_2 <= right._param_1 &&
        2 <= right._param_3 &&
        right._param_3 <= right._param_1 &&
        2 <= left._param_1_0 &&
        left._param_1_0 <= 100000 &&
        1 <= left._param_2_1 &&
        left._param_2_1 <= left._param_1_0 &&
        2 <= left._param_3_2 &&
        left._param_3_2 <= left._param_1_0 &&
        left._param_1_0 == right._param_1 &&
        left._param_2_1 == right._param_2 &&
        left._param_3_2 == right._param_3;
 * left:  LEFT_func8;
 * right: RIGHT_func12;
 * post:  left._ret_0_3 == right._ret_0;
 */

void _generator(int __param_1, int __param_2, int __param_3) {
  r__param_1 = __param_1;
  r__param_2 = __param_2;
  r__param_3 = __param_3;
  l__param_1_0 = __param_1;
  l__param_2_1 = __param_2;
  l__param_3_2 = __param_3;
}

void RIGHT_func12(int _param_1, int _param_2, int _param_3)
{
  int _local_4;
  int _local_5;
  _local_4 = (_param_1 / _param_2);
  if ((_local_4 >= _param_3))
  {
    _local_5 = _local_4;
    if ((_local_5 >= _param_3))
    {
      _local_5 = (_local_5 - _param_3);
      _local_4 = (_local_4 + 1);
      _local_5 = (_local_5 + 1);
    }
    while ((_local_5 >= _param_3))
    {
      _local_5 = (_local_5 - _param_3);
      _local_4 = (_local_4 + 1);
      _local_5 = (_local_5 + 1);
    }
  }
  int _ret_0 = _local_4;
}

void LEFT_func8(int _param_1_0, int _param_2_1, int _param_3_2)
{
  int _local_4_4;
  int _local_5_5;
  _local_4_4 = (_param_1_0 / _param_2_1);
  _local_5_5 = _local_4_4;
  while ((_param_3_2 <= _local_4_4))
  {
    _local_4_4 = (_local_4_4 - _param_3_2);
    _local_5_5 = (_local_5_5 + 1);
    _local_4_4 = (_local_4_4 + 1);
  }
  int _ret_0_3 = _local_5_5;
}
