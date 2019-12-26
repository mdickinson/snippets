def isqrt(n):
    c = (n.bit_length() - 1) // 2
    s = c.bit_length()
    d = 0
    a = 1
    while s > 0:
        e = d
        s = s - 1
        d = c >> s
        a = (a << d-e-1) + (n >> 2*c-d-e+1) // a
    return a if a*a <= n else a - 1
