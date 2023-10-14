void verifyfunc(unsigned l_B,unsigned l_C,unsigned l_N,
unsigned l_x,unsigned r_B,unsigned r_C,unsigned r_N, unsigned r_x )
{
    unsigned l_i = 0;
    unsigned r_i = 0;
    unsigned l_j = 0;
    unsigned r_j = r_C;
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