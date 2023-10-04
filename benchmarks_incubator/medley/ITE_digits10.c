/* @KESTREL
 * pre:   left.n == right.n;
 * left:  f0;
 * right: f1;
 * post:  left.result == right.retval;
 */

void f0(int n)
{
    int result = 1;
    n = n / 10;

    while (n > 0)
    {
        result = result + 1;
        n = n / 10;
    }
}

void f1(int n)
{
    int result;
    int b;
    result = 1;
    b = 1;
    int retval = -1;
    while (!(b == 0))
    {
        if (n < 10)
        {
            retval = result;
            b = 0;
        }
        else if (n < 100)
        {
            retval = result + 1;
            b = 0;
        }
        else if (n < 1000)
        {
            retval = result + 2;
            b = 0;
        }
        else if (n < 10000)
        {
            retval = result + 3;
            b = 0;
        }
        else
        {
            n = n / 10000;
            result = result + 4;
        }
    }
}
