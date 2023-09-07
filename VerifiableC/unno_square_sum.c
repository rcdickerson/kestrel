void verifyfunc(unsigned int l_a,unsigned int l_b, unsigned int l_c, 
 unsigned int r_a,unsigned int r_b, unsigned int r_c)
{
    for(;;)
    {
        if(l_a >= l_b)
        {
            break;
        }
        else if(r_a >= r_b)
        {
            break;
        }
        else
        {
            l_c = (l_c + (l_a * l_a));
            l_a = (l_a + 1);
            r_c = (r_c + (r_a * r_a));
            r_a = (r_a + 1);
        }
    }
    for(;;)
    {
        if(l_a >= l_b)
        {
            break;
        }
        else if(r_a < r_b)
        {
            break;
        }
        else
        {
            l_c = (l_c + (l_a * l_a));
            l_a = (l_a + 1);
        }
    }
    for(;;)
    {
        if(r_a >= r_b)
        {
            break;
        }
        else if(l_a < l_b)
        {
            break;
        }
        else
        {
            r_c = (r_c + (r_a * r_a));
            r_a = (r_a + 1);
        }
    }
}

int main(void) 
{
  unsigned int l_a = 4;
  unsigned int l_b = 5;
  unsigned int r_a = 4;
  unsigned int r_b = 5;
  unsigned int l_c = 0;
  unsigned int r_c = 0;
  verifyfunc(l_a,l_b, l_c,r_a, r_b,r_c);
  return 0;
 }