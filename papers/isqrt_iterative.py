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


# Loop invariants: at the beginning and end of the while loop we have:
#     d = c >> s
# and
#     a is a near square root of n >> 2*(c-d)


# Testing
def check_isqrt(n):
    a = isqrt(n)
    assert a * a <= n < (a + 1) * (a + 1)


for n in range(1, 10**7):
    check_isqrt(n)
