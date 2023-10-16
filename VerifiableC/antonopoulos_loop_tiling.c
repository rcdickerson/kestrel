void verifyfunc(unsigned a_1[100], unsigned a_2[10][10],unsigned f[100])
{
    unsigned r_i = 0;
    unsigned l_x = 0; 
    for(;;)
    {
        if(l_x >= 100)
        {
            break;
        }
        else if(r_i >= 10)
        {
            break;
        }
        else
        {
            a_1[l_x] = f[l_x];
            l_x = l_x + 1;
            unsigned r_j = 0;
            while (r_j < 10)
            {
                a_2[r_i][r_j] = f[(r_i * 10) + r_j];
                r_j = r_j + 1;
            }
            r_i = r_i + 1;
            if (r_i < 10) 
            {
                unsigned r_j = 0;
                while (r_j < 10) 
                {
                    a_2[r_i][r_j] = f[(r_i * 10) + r_j];
                    r_j = (r_j + 1);
                }
                r_i = (r_i + 1);
            }
        }
    }
    for(;;) 
    {
        if(l_x >= 100)
        {
            break;
        }
        else if(r_i < 10)
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
        if(l_x < 100)
        {
            break;
        }
        else if(r_i >= 10)
        {
            break;
        }
        else
        {
            unsigned r_j = 0;
            while (r_j < 10) 
            {
                a_2[r_i][r_j] = f[(r_i * 10) + r_j];
                r_j = (r_j + 1);
            }
            r_i = (r_i + 1);
        }
    }
}
