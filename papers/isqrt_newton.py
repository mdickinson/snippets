def isqrt(n):
    a = 1 << (n.bit_length() + 1) // 2
    while True:
        d = n // a
        if d >= a:
            return a
        a = (a + d) // 2


# Testing
def check_isqrt(n):
    a = isqrt(n)
    assert a * a <= n < (a + 1) * (a + 1)


for n in range(10**6):
    check_isqrt(n)


def measured_isqrt(n):
    divisions = 0
    if n == 0:
        return divisions

    a = 1 << (n.bit_length() + 1) // 2
    while True:
        d = n // a
        divisions += 1
        if d >= a:
            return divisions
        a = (a + d) // 2


best_so_far = -1
for n in range(2**32+1):
    divisions = measured_isqrt(n)
    if divisions > best_so_far:
        print("Worst case: ", n, divisions)
        best_so_far = divisions
    if n & (2**24-1) == 0:
        print("Progress:", n)
