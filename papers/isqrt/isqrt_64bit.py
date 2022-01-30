def isqrt(n):
    e = (64 - n.bit_length()) // 2
    m = n << 2*e
    a = 1 + (m >> 62)
    a = (a << 1) + (m >> 59) // a
    a = (a << 3) + (m >> 53) // a
    a = (a << 7) + (m >> 41) // a
    a = (a << 15) + (m >> 17) // a
    a = a >> e
    return a if a*a <= n else a - 1
