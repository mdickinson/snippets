def nsqrt(n):
    if n < 4:
        return 1
    else:
        e = (n.bit_length()-3) // 4
        a = nsqrt(n >> 2*e+2)
        return (a << e) + (n >> e+2) // a


def isqrt(n):
    a = nsqrt(n)
    return a if a*a <= n else a - 1
