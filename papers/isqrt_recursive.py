def nsqrt(n):
    if n < 4:
        return 1
    e = (n.bit_length()-3) // 4
    a = nsqrt(n >> 2*e+2)
    return (a << e) + (n >> e+2) // a


def isqrt(n):
    if n == 0:
        return 0
    a = nsqrt(n)
    if a*a <= n:
        return a
    else:
        return a-1


# Testing
def check_isqrt(n):
    a = isqrt(n)
    assert a * a <= n < (a + 1) * (a + 1)


for n in range(10**6):
    check_isqrt(n)
