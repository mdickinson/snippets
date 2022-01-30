def isqrt(n):

    def g(a):
        return (a + n//a) // 2

    a = n
    while True:
        ga = g(a)
        if a <= ga:
            return a
        a = ga
