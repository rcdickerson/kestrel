#include<stdlib.h>

void verifyfunc(int l_n, int r_n, int l_x, int r_x, int l_i, int r_i)
{
    for(;;)
    {
        if(l_i > l_n)
        {
            break;
        }
        else if(r_i > r_n)
        {
            break;
        }
        else
        {
            l_x = (l_x + 1);
            l_i = (l_i + 1);
            r_x = (r_x + 1);
            r_i = (r_i + 1);
        }
    }
    for(;;)
    {
        if(l_i > l_n)
        {
            break;
        }
        else if(r_i <= r_n)
        {
            break;
        }
        else
        {
            l_x = (l_x + 1);
            l_i = (l_i + 1);
        }
    }
    for(;;)
    {
        if(r_i > r_n)
        {
            break;
        }
        else if(l_i <= l_n)
        {
            break;
        }
        else
        {
            r_x = (r_x + 1);
            r_i = (r_i + 1);
        }
    }
}

int main(void)
{
    //all l and r variables
    int l_n = 4;
    int r_n = 4;
    int l_x = 0;
    int r_x = 0;
    int l_i = 0;
    int r_i = 0;
    verifyfunc(l_n,r_n,l_x,r_x,l_i,r_i);
    return 0;
}