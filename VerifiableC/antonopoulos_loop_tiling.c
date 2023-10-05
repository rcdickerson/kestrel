void verifyfunc(unsigned int l_x, unsigned int r_x, unsigned int M,
unsigned a_1[100], unsigned a_2[100],unsigned f[100])
{ 
    for(;;)
    {
        if(l_x >= M)
        {
            break;
        }
        else if(r_x >= M)
        {
            break;
        }
        else
        {
            a_1[l_x] = f[l_x];
            a_2[r_x] = f[r_x];
            l_x = (l_x + 1);
            r_x = (r_x + 1);
        }
    }
    for(;;) 
    {
        if(l_x >= M)
        {
            break;
        }
        else if(r_x < M)
        {
            break;
        }
        else
        {
            a_1[l_x] = f[l_x];
            l_x = (l_x + 1);
        }
    }
    for(;;)
    {
        if(l_x < M)
        {
            break;
        }
        else if(r_x >= M)
        {
            break;
        }
        else
        {
            a_2[r_x] = f[r_x];
            r_x = (r_x + 1);
            
        }
    }
}

unsigned a_1[100];
unsigned a_2[100];
unsigned f[100];

int main(void)
{
    unsigned int M = 100;
    int r_x = 0;
    int l_x = 0;
    return 0;
}