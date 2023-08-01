/* @KESTREL
 * pre:   left._param_1_0 >= 0 &&
          right._param_1 >= 0 &&
          left._param_1_0 == right._param_1;
 * left:  LEFT_func6;
 * right: RIGHT_func10;
 * post:  left._ret_0_1 == right._ret_0;
 */

void RIGHT_func10(int _param_1)
{
  int inlined__param_1_0;
  int inlined__ret_0_1;
  int inlined__local_2_2;
  int _tmpret_2;
  while ((_param_1 >= 10))
  {
    inlined__param_1_0 = _param_1;
    inlined__local_2_2 = 0;
    while ((inlined__param_1_0 != 0))
    {
      inlined__local_2_2 = (inlined__local_2_2 + (inlined__param_1_0 % 10));
      inlined__param_1_0 = (inlined__param_1_0 / 10);
    }
    inlined__ret_0_1 = inlined__local_2_2;
    _tmpret_2 = inlined__ret_0_1;
    _param_1 = _tmpret_2;
  }
  int _ret_0 = _param_1;
}

void LEFT_func6(int _param_1_0)
{
  int _local_2;
  int _local_3;
  _local_2 = _param_1_0;
  while ((_local_2 >= 10))
  {
    _local_3 = _local_2;
    _local_2 = 0;
    while (((_local_3 / 10) >= 1))
    {
      _local_2 = (_local_2 + (_local_3 % 10));
      _local_3 = (_local_3 / 10);
    }
    _local_2 = (_local_2 + _local_3);
  }
  int _ret_0_1 = _local_2;
}
