/* @KESTREL
 * pre:   1 <= right._param_1 &&
          right._param_1 <= 1000 &&
          1 <= right._param_1 &&
          right._param_1 <= 1000 &&
          left._param_1_0 == right._param_1 &&
          left._param_2_1 == right._param_2 &&
          left._param_3.2 == right._param_3;
 * left:  LEFT_func11;
 * right: RIGHT_func17;
 * post:  left._param_2_1 == right._param_2 &&
          left._param_3_2 == right._param_3;
 */

void RIGHT_func17(int _param_1, int* _param_2, int* _param_3)
{
  int _local_4;
  int _local_5;
  int _local_6;
  int _local_7;
  int _local_8;
  int _local_9;
  _local_4 = _param_2[0];
  _local_5 = _param_2[0];
  _local_6 = 0;
  _local_7 = 0;
  _local_8 = 1;
  while (_local_8 < _param_1)
  {
    if ((_param_2[_local_8] > _local_5))
    {
      _local_5 = _param_2[_local_8];
      _local_6 = (_local_6 + 1);
    }
    _local_8 = _local_8 + 1;
  }
  _local_9 = 1;
  while (_local_9 < _param_1)
  {
    if ((_param_2[_local_9] < _local_4))
    {
      _local_4 = _param_2[_local_9];
      _local_7 = (_local_7 + 1);
    }
    _local_9 = _local_9 + 1;
  }
  _param_3[0] = _local_6;
  _param_3[1] = _local_7;
}

void LEFT_func11(int _param_1_0, int* _param_2_1, int* _param_3_2)
{
  int _local_4_3;
  int _local_5_4;
  int _local_6_5;
  int _local_7_6;
  int _local_8_7;
  _local_4_3 = 0;
  _local_5_4 = 0;
  _local_6_5 = _param_2_1[0];
  _local_7_6 = _param_2_1[0];
  _local_8_7 = 1;
  while (_local_8_7 < _param_1_0)
  {
    if ((_param_2_1[_local_8_7] > _local_6_5))
    {
      _local_6_5 = _param_2_1[_local_8_7];
      _local_4_3 = (_local_4_3 + 1);
    }
    if ((_param_2_1[_local_8_7] < _local_7_6))
    {
      _local_7_6 = _param_2_1[_local_8_7];
      _local_5_4 = (_local_5_4 + 1);
    }
    _local_8_7 = _local_8_7 + 1;
  }
  _param_3_2[0] = _local_4_3;
  _param_3_2[1] = _local_5_4;
}
