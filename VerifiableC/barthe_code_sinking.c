
void verifyfunc(unsigned l_a[11], unsigned r_a[11])
{
  unsigned l_max = l_a[0];
  unsigned lind = 0;
  unsigned l_i = 1;
  unsigned r_max = r_a[0];
  unsigned rind = 0;
  unsigned r_i = 1;
  for(;;)
  {
      if(l_i >= 11)
      {
        break;
      }
      else if(r_i >= 11)
      {
        break;
      }
      else
      {
          if(l_max < l_a[l_i])
          {
            l_max = l_a[l_i];
            lind = l_i;
          }
          if(r_max < r_a[r_i])
          {
            r_max = r_a[r_i];
            rind = r_i;
          }
          if(r_i == 10)
          {//swap here
            unsigned t = r_a[10];
            r_a[10] = r_a[rind];
            r_a[rind] = t;
          }
          r_i = r_i + 1;
          l_i = l_i + 1;
      }
  }
  for(;;)
  {
    if(l_i >= 11)
    {
      break;
    }
    else
    {
          if(l_max < l_a[l_i])
          {
            l_max = l_a[l_i];
            lind = l_i;
          }
          l_i = l_i + 1;

    }
  }
  for(;;)
  {
    if(r_i >= 11)
    {
      break;
    }
    else
    {
          if(r_max < r_a[r_i])
          {
            r_max = r_a[r_i];
            rind = r_i;
          }
          if(r_i == 10)
          {
            unsigned t = r_a[10];
            r_a[10] = r_a[rind];
            r_a[rind] = t;
          }
          r_i = r_i + 1;
    }
  }
  //swap
  unsigned t = l_a[10];
  l_a[10] = l_a[lind];
  l_a[lind] = t;
}