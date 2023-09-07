void verifyfunc(unsigned int l_B,unsigned int l_C,unsigned int l_N,
unsigned int l_x,unsigned int r_B,unsigned int r_C,unsigned int r_N,
unsigned int r_x,unsigned int l_i,unsigned int l_j,unsigned int r_i,unsigned int r_j)
{
    for(;;)
    {
        if(l_i >= l_N)
        {
            break;
        }
        else if(r_i >= r_N)
        {
            break;
        }
        else
        {
            l_j = ((l_i * l_B) + l_C);
            l_x = (l_x + l_j);
            l_i = (l_i + 1);
            r_x = (r_x + r_j);
            r_j = (r_j + r_B);
            r_i = (r_i + 1);

        }
    }
    for(;;)
    {
        if(l_i >= l_N)
        {
            break;
        }
        else if(r_i < r_N)
        {
            break;
        }
        else
        {
            l_j = ((l_i * l_B) + l_C);
            l_x = (l_x + l_j);
            l_i = (l_i + 1);
        }
    }
    for(;;)
    {
        if(l_i < l_N)
        {
            break;
        }
        else if(r_i >= r_N)
        {
            break;
        }
        else
        {
            r_x = (r_x + r_j);
            r_j = (r_j + r_B);
            r_i = (r_i + 1);
        }
    }
}

int main(void) 
{
    unsigned int l_B = 5;
    unsigned int l_C = 4;
    unsigned int l_N = 3;
    unsigned int l_x = 2;
    unsigned int r_B = 5;
    unsigned int r_C = 4;
    unsigned int r_N = 3;
    unsigned int r_x = 2;
    unsigned int l_i = 0; //explicit assign
    unsigned int l_j = 0; //explicit assign
    unsigned int r_i = 0; //explicit assign
    unsigned int r_j = r_C; //explicit assign
    verifyfunc(l_B,l_C,l_N,l_x,r_B,r_C,r_N,r_x,l_i,l_j,r_i,r_j);
    return 0;
 }