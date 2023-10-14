void verifyfunc(unsigned l_a,unsigned l_b,unsigned r_a,unsigned r_b)
{
    unsigned l_c = 0;
    unsigned r_c = 0;
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