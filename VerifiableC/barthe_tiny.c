
void verifyfunc(unsigned l_a[100],unsigned l_b[100])
{
  unsigned int l_i = 0;
  for(;;)
  {
      if(l_i >= 100)
      {
        break;
      }
      else
      {
          l_b[l_i] = l_b[l_i] + l_a[l_i];
          l_a[l_i] = l_a[l_i] + 1;
          l_i = l_i + 1;
      }
  }  
}


void verifyfunca(unsigned l_a[100],unsigned l_b[100])
{
  unsigned int l_i = 0;
  for(;;)
  {
      if(l_i >= 100)
      {
        break;
      }
      else
      {
          l_a[l_i] = l_a[l_i] + 1;
          l_b[l_i] = l_b[l_i] + l_a[l_i];
          l_i = l_i + 1;
      }
  }  
}

void verifyfuncc(unsigned l_a[100],unsigned l_b[100], unsigned l_c[100])
{
  unsigned int l_i = 0;
  for(;;)
  {
      if(l_i >= 100)
      {
        break;
      }
      else
      {
          l_a[l_i] = l_a[l_i] + 1;
          l_b[l_i] = l_b[l_i] + l_a[l_i];
          l_c[l_i] = l_c[l_i] + l_b[l_i];
          l_i = l_i + 1;
      }
  }  
}