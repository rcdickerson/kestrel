#include "seahorn/seahorn.h"
extern int arb_int();
const int left_o1_length = 10;
const int left_o2_length = 15;
int left_o1[left_o1_length];
int left_o2[left_o2_length];
const int right_o1_length = 15;
const int right_o2_length = 10;
int right_o1[right_o1_length];
int right_o2[right_o2_length];

void main() {
  int _i = 1;
  while (_i < left_o1_length) {
    assume(left_o1[_i] == right_o2[_i]);
    _i = (_i + 1);
  }
  int _j = 1;
  while (_j < left_o2_length) {
    assume(left_o2[_j] == right_o1[_j]);
    _j = (_j + 1);
  }
  int l_ret = -999;
  int l_index;
  int l_aentry;
  int l_bentry;
  l_index = 0;
  while ((l_index < left_o1_length) && (l_index < left_o2_length)) {
    l_aentry = left_o1[l_index];
    l_bentry = left_o2[l_index];
    if (l_aentry < l_bentry) {
      l_ret = (-1);
      break;
    }
    if (l_aentry > l_bentry) {
      l_ret = 1;
      break;
    }
    l_index = (l_index + 1);
  }
  if (l_ret == (-999)) {
    if (left_o1_length < left_o2_length) {
      l_ret = (-1);
    }
    if (left_o1_length > left_o2_length) {
      l_ret = 1;
    }
    l_ret = 0;
  }
  int r_ret = -999;
  int r_index;
  int r_aentry;
  int r_bentry;
  r_index = 0;
  while ((r_index < right_o1_length) && (r_index < right_o2_length)) {
    r_aentry = right_o1[r_index];
    r_bentry = right_o2[r_index];
    if (r_aentry < r_bentry) {
      r_ret = (-1);
      break;
    }
    if (r_aentry > r_bentry) {
      r_ret = 1;
      break;
    }
    r_index = (r_index + 1);
  }
  if (r_ret == (-999)) {
    if (right_o1_length < right_o2_length) {
      r_ret = (-1);
    }
    if (right_o1_length > right_o2_length) {
      r_ret = 1;
    }
    r_ret = 0;
  }
  sassert(l_ret == (-1 * r_ret));
 }
