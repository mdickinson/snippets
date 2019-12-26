def isqrt(n):
    a = 1 << (n.bit_length() + 1) // 2
    while True:
        d = n // a
        if a <= d:
            return a
        a = (a + d) // 2
