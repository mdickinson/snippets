"""
Integer square root
===================
There are many applications that call for an integer square root: a function
which, given a nonnegative integer ``n``, returns the integer part of the
square root of ``n``. To take just one example, when testing a small integer
``n`` for primality using trial division, it suffices to check divisors up to
and including the integer square root of ``n``.

In this module we present algorithms and analysis for computing
this integer square root.

In the discussion below, we'll ignore the cases of negative and zero inputs,
since these are easily dealt with. We concentrate on the case of a positive
integer argument ``n``.

Floating-point-based methods
----------------------------
The following implementation seems like an obvious one::

    from math import sqrt

    def isqrt(n):
        return int(sqrt(n))

However, this suffers from a number of drawbacks:

1. The call ``sqrt(n)`` involves an implicit conversion of the integer ``n``
   to a ``float``. Since the ``float`` type has limited precision, this
   conversion could potentially lose information for larger ``n``. For example,
   on a typical machine, the values ``n = 10**16`` and ``n = 10**16 - 1``
   become the same when converted to ``float``, so the above implementation
   of ``isqrt`` will give the same value for both. But they have different
   integer square roots, so ``isqrt`` must necessarily be wrong for at least
   one of them::

        >>> from math import sqrt
        >>> def isqrt(n): return int(sqrt(n))
        ...
        >>> isqrt(10**16)
        100000000
        >>> isqrt(10**16 - 1)
        100000000

   Assuming IEEE 754 binary64 format floating-point, the implicit conversion
   will be exact for all values up to ``n = 2**53``.

2. The above affects larger values of ``n``. But even for small ``n``, if
   the ``sqrt`` function is not correctly rounded, then the value returned
   by ``sqrt(k*k)`` could potentially be smaller than ``k``. If that happens,
   even if it's out by only a single unit in the last place, we end up with
   a result of ``k - 1`` instead of the correct ``k``.

3. For ``n`` exceeding the range of a ``float``, this method is completely
   useless: we don't even get an approximate answer; instead, we get an
   ``OverflowError``.

        >>> isqrt(2**1024)
        Traceback (most recent call last):
        File "<stdin>", line 1, in <module>
        File "<stdin>", line 1, in isqrt
        OverflowError: int too large to convert to float

For small ``n`` (say, smaller than 10**12), only the second item above is a
potential issue. We can mitigate the risk from a non-correctly-rounded
``math.sqrt`` implementation by offsetting ``n``::

    def isqrt(n):
        return int(sqrt(n + 0.5))

How much safety from a badly-rounded square root does this give us? Let's
assume that we're working with IEEE 754 binary64 format (precision 53).

Proposition. Suppose n is a positive integer and 2**(k-1) <= √n < 2**k for an
integer k. Then if sqrt(n+0.5) is computed with an error not exceeding
2**(51-2k) ulps, floor(sqrt(n+0.5)) == floor(√n).

Proof of the proposition. Write ``s`` for the value ``sqrt(n + 0.5)``, and
``e`` for the absolute error involved in computing ``s``, so::

    s = √(n+1/2) + e

We have 2**(k-1) < √(n+1/2) < 2**k, and in this interval, 1ulp is 2**(k-53),
so our assumption on the error translates to::

    |e| <= 2**(-k-2)

Now √(n+1) <= 2**k, so it follows that::

    2**(-k-2) <= 1 / 4√(n+1)

and hence that

    |e| <= 1 / 4√(n+1)

But it's also easily checked that:

    1 / 4√(n+1) < √(n+1) - √(n+1/2) < √(n+1/2) - √n

and hence that e < √(n+1) - √(n+1/2) and -e < √(n+1/2) - √n, so

    √n < s < √(n+1)

So floor(√n) <= floor(s), and floor(s) < √(n+1). Hence floor(s)**2 < n + 1,
so floor(s)**2 <= n, and floor(s) <= √n, so floor(s) <= floor(√n). Hence the
result.

Corollary. If n < 2**50 and ``sqrt`` is accurate to within <= 2 ulps, then
floor(sqrt(n + 0.5)) == floor(√n).

Proof. Apply the proposition with ``k = 25``.

Corollary. If n < 2**52 and ``sqrt`` is correctly rounded, then
floor(sqrt(n+0.5)) == floor(√n).

Proof. If ``sqrt`` is correctly rounded, then ``sqrt(n+0.5)`` is computed
with an error not exceeding 0.5 ulps. Now apply the proposition with
``k = 26``.

The result of the corollary is tight. Given ``n = (2**26 + 1)**2 - 1``,
under IEEE 754 binary64 arithmetic and correctly-rounded square root, we
have ``sqrt(n) = 2**26 + 1``, so ``int(sqrt(n))`` gives the wrong answer,
as does ``int(sqrt(n + 0.5))``.

Proposition. Suppose we're using IEEE 754 binary64 arithmetic and sqrt is
correctly rounded. Then if 0 < n < 2**106, and m is the closest representable
IEEE 754 binary64 float to n, |sqrt(m) - √n| < 1.

Proof (Sketch). Show that |√m - √n| < 1/2 and |sqrt(m) - √m| <= 1/2.

As a corollary, if we know in advance that ``n`` is a perfect square, then
``sqrt(m)`` will exactly recover its square root.

So we can use this as a starting-point for the recursive algorithm.

Recursive square root
---------------------
The Newton method for computing an integer square root is wasteful,
in that the initial steps are needlessly performed with full precision.
Instead, it should be possible to increase the precision gradually,
only reaching full precision for the last one or two iteration.

Investigating this leads to a recursive implementation based on
the Newton iteration. Here's the necessary statement that makes
the recursion work.

Proposition. Let n and k be positive integers satisfying

    4**(2k-2) <= n < 4**(2k+2)

Suppose that a is an approximation to 2√(n//4**k) satisfying

    |a - 2√(n//4**k)| < 1

Let b = 2**(k-1)a + n // 2**(k-1)a. Then b is an approximation to 2√n
satisfying

    |b - 2√n| < 1

Proof. First note that we can replace the integer division in the assumption
with true division: |a - 2√(n//4**k)| < 1 implies |a - 2√(n/4**k)| < 1.








Suppose that 4**(2k-2) <= n < 4**(2k+2), for some positive integer k.
And suppose that we have an integer a satisfying

   | a - √(n//4**k) | < 1

It's easy to show that this implies

   | a - √(n/4**k) | < 1

or equivalently

   | 2**k a - √n | < 2**k

and from there deduce that

   0 < (2**k a + n / (2**k a))/2 - √n < 1

and hence that

   -1 < floor(2**k a + n / (2**k a)) - √n < 1






"""

# Algorithm notes
# ---------------
# Assume that n is a nonnegative integer. We want to find the integer square
# root of n. We use the following method based on Newton-Raphson.
#
# Notation. Write isqrt(n) for the floor of the sqrt of n, and x // y for the
# floor of x divided by y.
#
# Suppose that a is any integer satisfying isqrt(n) <= a. Then the following
# are true:
#
# (1) If n // a >= a, then isqrt(n) = a.
# (2) If n // a < a, then isqrt(n) <= (a + n // a) // 2 < a.
#
# This gives a simple algorithm: compute n // a. If it's greater than or equal
# to a, we have the result; otherwise, we have a new estimate that's closer to
# isqrt(n) than a was. Repeat with that new estimate.
#
# Proof of (1): n // a >= a if and only if n / a >= a, which is equivalent
# to sqrt(n) >= a, which in turn is equivalent to isqrt(n) >= a. Since we're
# assuming that a >= isqrt(n), the result follows.
#
# Proof of (2): the second inequality is clear; we only need to justify the
# first. But the AM-GM inequality applied to a and n / a gives:
#
#     sqrt(n) <= (a + n / a) / 2
#
# Now taking floors of both sides of the inequality gives the result.
#
# For the algorithm below to work, we also need a starting guess that's
# greater than or equal to floor(sqrt(n)). There are a few ways to do this.
# We could simply pick n, but that leads to a lot of wasted iterations for
# large n. A value that's easy to compute and doesn't require floating-point
# arithmetic is the largest power of 2 exceeding the square root of n. We have:
#
#      sqrt(n) < 2**k iff
#      n < 2**2k iff
#      n.bit_length() <= 2k iff
#      ceil(n.bit_length() / 2) <= k
#
# So we can use 1 << -(-n.bit_length() // 2) as our starting guess. Technically
# we could replace n with n - 1 here, but this will only make a difference for
# powers of 4, so it doesn't seem worth the extra operation.
#
# We can also easily satisfy the condition that a >= floor(sqrt(n)) by
# making sure that we perform at least one iteration. So we could pick _any_
# positive integer b (preferably one close to the actual square root) and then
# use a = (b + n // b) // 2 as our starting value.
#
# Improved termination condition
# ------------------------------
# From the above analysis, the obvious termination condition to use is:
#
#   n // a >= a
#
# However, it's quite common (depending on the size of n) for the
# penultimate division to give a value n // a satisfying
#
#   n // a == a - 1
#
# In that case, we can avoid an extra iteration and an expensive division:
# if n // a == a - 1 then:
#
#   a - 1 <= n / a < a
#
# so
#
#   a*a - a <= n < a * a
#
# and assuming a is positive, this implies that
#
#   (a-1) ** 2 <= n < a**2
#
# hence that isqrt(n) == a - 1.
#
# However, it's not immediately clear whether this is a win overall. As n
# increases, the chance of hitting the early termination condition decreases,
# and we're paying the price of the extra test on every call. The choice of
# whether to implement this or not probably depends on likely call patterns.
#
# We choose not to implement this improved
# termination condition in the code below, to keep things simple.
#
# Complexity analysis
# -------------------
# As with the usual Newton-Raphson algorithm, convergence is quadratic (at
# least up to the final step). Here we try to get a concrete bound on the
# number of steps involved.
#
# What's a step? Well, for large n, the most time-consuming step in the
# algorithm is the division n // a. Everything else is at worst linear time. So
# let's count the number of divisions n // a performed by algorithm.
# Equivalently, we're counting iterations of the ``while`` loop, including
# the final part-iteration.
#
# In the usual Newton iteration with a_next = (a_current + n/a_current)/2,
# the relative error r = (a - sqrt(n)) / sqrt(n) follows the rule:
#
#     r_next = r_current**2 / (2 + 2*r_current)
#
# So for example if the initial relative error is exactly 1, the relative error
# on the next step is exactly 1/4, and on the step after that it's 1/40, then
# 1/3280, etc. The sequence of denominators here is https://oeis.org/A059918.
# Let's write Q(n) for the nth denominator. So Q(0) = 1, Q(1) = 4,
# Q(2) = 40, Q(3) = 3280, etc.
#
# In our integer version of the algorithm, the relative error will decrease at
# least this fast, and possibly slightly faster, thanks to the floor
# operations. Our initial estimate based on a power of two always gives us a
# starting relative error that's at most 1.
#
# Now suppose that (for example) n <= 3280**2 == 10758400. Then after three
# iterations we have a value a with relative error at most 1/3280. Hence
# a - sqrt(n) <= 1/3280 sqrt(n) <= 1, so after three steps we're guaranteed
# to be within 1 of the target value, and we're guaranteed to hit isqrt(n)
# within four steps (since each step decreases the value of a). It may
# then take a fifth division to verify the stopping condition. So we need
# at most 5 divisions for any n <= 10758400.
#
# Conversely, there are plenty of examples of values n <= 10758400 which do
# need the full 5 divisions. The first such is n = 4224. The sequence of
# estimates, along with their relative errors, goes:
#
#   a = 128, r =  0.969464
#   a =  80, r =  0.230915
#   a =  66, r =  0.015505
#   a =  65, r =  0.000118
#   a =  64, r = -0.015268
#
# So for small n, we have the following bounds on the number of divisions
# needed:
#
#          n at most  |  max divisions
#                 16  |  3
#               1600  |  4
#           10758400  |  5
#    463255025689600  |  6
#           8.58e+29  |  7
#           2.94e+60  |  8
#
# A brute-force search shows that the first n requiring 3 divisions is 8,
# the first n requiring 4 divisions is 80, the first n requiring 5 divisions
# is 4224, and the first n requiring 6 divisions is 16785408 (=4097**2 - 1).
#
# In general, if sqrt(n) <= Q(k), then we need at most k+2 divisions to
# find isqrt(n). There's an easily-proved closed form for Q(k):
#
#   Q(k) = (3**(2**k) - 1) // 2
#
# We can use this to bound the number of divisions required in terms of n:
#
#    divisions <= 2 + ceil(log2(log3(2*sqrt(n) + 1)))

import math


def _isqrt_approx(n):
    """
    Integer approximation to the integer square root of n.

    For a positive integer ``n``, use ``math.sqrt`` to compute an approximation
    to the integer square root of ``n``.

    This function makes no assumptions about the accuracy of ``math.sqrt``. For
    ``n`` smaller than ``2**52``, the returned approximation is *likely* to be
    exact on a typical machines, and for ``n`` larger than ``2**52``, it's
    *likely* to be accurate to at least 52 significant bits, but neither of
    these properties is guaranteed. The only guarantee made by this function is
    that the return value will be a positive integer.
    """
    try:
        s = int(math.sqrt(n))
    except OverflowError:
        shift = n.bit_length() // 2 - 53
        s = int(math.sqrt(n >> 2 * shift)) << shift
    return max(s, 1)


def _isqrt_newton(n, s):
    """
    Integer square root via Newton's method.

    Compute the integer square root of ``n``, using Newton's method with
    an initial guess of ``s``. Assumes that ``n`` and ``s`` are both
    positive integers.
    """
    # Ensure that a is an upper bound for isqrt(n), and do an early return
    # that covers most cases where a is exactly equal to isqrt(n).
    d = n // s
    a = (s + d) // 2
    if a == s:
        return a

    while True:
        # Invariant: a >= isqrt(n)
        d = n // a
        if d >= a:
            return a
        a = (a + d) // 2


def isqrt(n):
    """
    Integer square root, via Newton's method.

    Parameters
    ----------
    n : int
        Input to find the square root of.

    Returns
    -------
    a : int
        Largest integer satisfying a * a <= n. Equivalently, the floor of
        the square root of n.

    Raises
    ------
    ValueError
        If n is negative.
    """
    if n < 0:
        raise ValueError("Square root of negative number")
    elif n == 0:
        return 0
    else:
        return _isqrt_newton(n, _isqrt_approx(n))


def isqrt_pure(n):
    """
    Integer square root, computed without any use of floating-point arithmetic.

    Parameters
    ----------
    n : int
        Input to find the square root of.

    Returns
    -------
    a : int
        Largest integer satisfying a * a <= n. Equivalently, the floor of
        the square root of n.

    Raises
    ------
    ValueError
        If n is negative.
    """
    if n < 0:
        raise ValueError("Square root of negative number")
    elif n == 0:
        return 0

    a = 1 << -(-n.bit_length() // 2)
    while True:
        d = n // a
        if d >= a:
            return a
        a = a + d >> 1


def _isqrt_recursive_pure(n):
    """
    Given a positive integer n, return an integer a
    such that (a - 1)**2 < n < (a + 1)**2.

    This function avoids any use of floating-point arithmetic.
    """
    b = n.bit_length() - 3
    if b < 0:
        return 1
    else:
        k = b >> 2
        m = n >> k + 2
        a = _isqrt_recursive_pure(m >> k)
        return (a << k) + m // a


def _isqrt_recursive(n):
    """
    Given a positive integer n, return an integer a
    such that (a - 1)**2 < n < (a + 1)**2.
    """
    b = n.bit_length()
    if b <= 106:
        a = int(math.sqrt(n))
        # If we knew that math.sqrt is correctly rounded and that the
        # floating-point format is IEEE 754 binary 64, we could simply
        # return a here. As it is, we have to check.
        return a if abs(n - a*a - 1) < 2*a else _isqrt_recursive_pure(a)
    else:
        k = b - 3 >> 2
        m = n >> k + 2
        a = _isqrt_recursive(m >> k)
        return (a << k) + m // a


def isqrt_recursive(n):
    """
    Integer square root via recursive method.
    """
    if n < 0:
        raise ValueError("Square root of negative number")
    elif n == 0:
        return 0

    a = _isqrt_recursive(n)
    return a - (n < a*a)


def isqrt_recursive_pure(n):
    """
    Integer square root via recursive method, with no use of floating-point.
    """
    if n < 0:
        raise ValueError("Square root of negative number")
    elif n == 0:
        return 0

    a = _isqrt_recursive_pure(n)
    return a - (n < a*a)


# Table of integer square roots with remainder up to 255 (inclusive).
ISQRTS = [(i, j) for i in range(16) for j in range(2*i+1)]


def isqrt_bytes(n):
    """
    Byte-by-byte implementation of integer square root.
    """
    if n < 0:
        raise ValueError("Square root of negative number")
    elif n == 0:
        return 0

    # Shift so that first byte is >= 64.
    q, r = divmod(-n.bit_length(), 8)
    shift = r // 2
    nbytes = iter((n << 2*shift).to_bytes(-q, "big"))

    a, r = ISQRTS[next(nbytes)]
    for b in nbytes:
        r = (r << 8) + b
        c = a << 5
        d, r = divmod(r, c)
        r -= d * d
        if r < 0:
            r += 2*d + c - 1
            d -= 1
        a = (a << 4) + d

    return a >> shift
