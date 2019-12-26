def isqrt(n):

    def g(a):
        return (a + n//a) // 2

    a = n
    while True:
        ga = g(a)
        if a <= ga:
            return a
        a = ga


# Testing
def check_isqrt(n):
    a = isqrt(n)
    assert a * a <= n < (a + 1) * (a + 1)


for n in range(1, 10**6):
    check_isqrt(n)
