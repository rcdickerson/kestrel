/* @KESTREL
 * pre:   left.n == right.n;
 * left:  f0;
 * right: f1;
 * post:  left.x == right.x;
 */

void f0(int n)
{
    int i;
    int x = 1;
    i = 1;
    while (i <= n)
    {
        x = x * 1;
        i = i + 1;
    }

    i = 0;
    while (i <= n)
    {
        x = x + i;
        i = i + 1;
    }

    i = 1;
    while (i <= n)
    {
        x = x * 2;
        i = i + 1;
    }
}

void f1(int n)
{
    int i;
    int x = 1;
    i = 1;
    while (i <= n)
    {
        x = x * 1;
        i = i + 1;
    }

    i = 1;
    while (i <= n)
    {
        x = x + i;
        i = i + 1;
    }

    i = 1;
    while (i <= n)
    {
        x = x * 2;
        i = i + 1;
    }
}
