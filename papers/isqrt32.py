def isqrt(n):
    e = (32 - n.bit_length()) // 2
    m = n << 2*e
    a = 1 + (m >> 30)
    a = (a << 1) + (m >> 27) // a
    a = (a << 3) + (m >> 21) // a
    a = (a << 7) + (m >> 9) // a
    a = a >> e
    return a if a*a <= n else a - 1


def check_isqrt(n):
    a = isqrt(n)
    assert a * a <= n < (a + 1) * (a + 1)


import random
ntrials = 1000000
for _ in range(ntrials):
    e = random.randint(1, 32)
    n = 2**(e-1) + (random.getrandbits(e - 1) if e >= 2 else 0)
    check_isqrt(n)
