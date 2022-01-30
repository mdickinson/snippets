import math


def isqrt(n):
    c = (n.bit_length() - 1) // 2
    s = (c//53).bit_length()
    d = c >> s
    a = int(math.sqrt(n >> 2*c-2*d))
    while s > 0:
        e = d
        s = s - 1
        d = c >> s
        a = (a << d-e-1) + (n >> 2*c-d-e+1) // a
    return a if a*a <= n else a - 1
