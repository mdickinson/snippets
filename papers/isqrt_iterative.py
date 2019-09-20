def isqrt(n):
    """Integer square root of a nonnegative integer."""
    if n == 0:
        return 0
    c = (n.bit_length() - 1) // 2
    m = c.bit_length()

    a = 1
    for s in range(1, m+1):  # s goes from 1 to m, inclusive
        d = c >> m-s
        e = d >> 1
        a = (a << d-e-1) + (n >> 2*c-d-e+1) // a
    return a if a*a <= n else a - 1


# Loop invariants: before the redefinition of a we have
#
#        assert (a - 1)**2 < n >> 2*(c-e) < (a + 1)**2
#
# and after we have
#
#        assert (a - 1)**2 < n >> 2*(c-d) < (a + 1)**2

# Testing
def check_isqrt(n):
    a = isqrt(n)
    assert a * a <= n < (a + 1) * (a + 1)


for n in range(10**6):
    check_isqrt(n)
