def iroot(n, k):
    """
    Return the integer part of the kth root of n.

    Parameters
    ----------
    n, k : int

    Returns
    -------
    a : int
        Largest integer satisfying a**k <= n < (a + 1)**k

    Raises
    ------
    ValueError
        If n is negative or k is not positive.
    """
    if n < 0 or k < 1:
        raise ValueError("n should be nonnegative and k should be positive")
    elif n == 0:
        return 0

    a = 1 << -(-n.bit_length() // k)
    while True:
        d = n // a ** (k - 1)
        if d >= a:
            return a
        a += (d - a) // k
