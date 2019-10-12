def isqrt(n):
    def f(a):
        return (a + n//a) // 2

    # Starting guess can be anything not
    # smaller than the integer square root.
    a = n
    while True:
        fa = f(a)
        if fa >= a:
            return a
        a = fa


# Testing
def check_isqrt(n):
    a = isqrt(n)
    assert a * a <= n < (a + 1) * (a + 1)


for n in range(1, 10**6):
    check_isqrt(n)
