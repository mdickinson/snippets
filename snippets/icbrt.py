def _icbrt_approx(n):
    """
    Integer approximation to the integer cube root of n.

    Assumes that ``n`` is a positive integer.

    On a machine with a reasonably accurate``pow`` implementation, this
    function *should* return accurate results for small ``n``. However, no
    guarantees are made about the accuracy of the result. The only guarantee is
    that the result will be a positive integer.
    """
    try:
        s = int((n + 0.5) ** (1/3))
    except OverflowError:
        shift = n.bit_length() // 3 - 53
        s = ((n >> 3 * shift) ** (1/3)) << shift
    return max(s, 1)


def _icbrt_newton(n, s):
    """
    Integer cube root via Newton's method.

    Compute the integer cube root of ``n`` via Newton's method, using
    a starting value of ``s``. Assumes that both ``n`` and ``s`` are
    positive integers.
    """
    d = n // (s * s)
    a = s + (d - s) // 3
    # Early return covering most of the cases where ``s`` is already the
    # correct answer.
    if a == s:
        return a

    while True:
        d = n // (a * a)
        if d >= a:
            return a
        a += (d - a) // 3


def icbrt(n):
    """
    Integer cube root.

    Given a nonnegative integer n, return the largest integer a satisfying
    a**3 <= n.

    Parameters
    ----------
    n : nonnegative int

    Returns
    -------
    a : int
        Largest integer satisfying a**3 <= n. Equivalently, the floor of the
        cube root of n.

    Raises
    ------
    ValueError
        If n is negative.
    """
    if n < 0:
        raise ValueError("Cube root of negative number")
    elif n == 0:
        return 0

    return _icbrt_newton(n, _icbrt_approx(n))


def icbrt_pure(n):
    """
    Integer cube root.

    Given a nonnegative integer n, return the largest integer a satisfying
    a**3 <= n.

    Parameters
    ----------
    n : nonnegative int

    Returns
    -------
    a : int
        Largest integer satisfying a**3 <= n. Equivalently, the floor of the
        cube root of n.

    Raises
    ------
    ValueError
        If n is negative.
    """
    # Implementation is entirely analogous to that of isqrt; the key inequality
    # comes from the AM-GM inequality applied to a, a and n/a.
    if n < 0:
        raise ValueError("Cube root of negative number")
    elif n == 0:
        return 0

    a = 1 << -(-n.bit_length() // 3)
    while True:
        d = n // (a * a)
        if d >= a:
            return a
        a += (d - a) // 3
