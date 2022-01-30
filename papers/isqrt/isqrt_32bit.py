def isqrt(n):
    e = (32 - n.bit_length()) // 2
    m = n << 2*e
    a = 1 + (m >> 30)
    a = (a << 1) + (m >> 27) // a
    a = (a << 3) + (m >> 21) // a
    a = (a << 7) + (m >> 9) // a
    a = a >> e
    return a if a*a <= n else a - 1
