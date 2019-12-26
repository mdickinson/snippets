import random
import unittest

import isqrt_heron_direct
import isqrt_heron_improved
import isqrt_recursive
import isqrt_iterative
import isqrt_32bit
import isqrt_64bit
import isqrt_accelerated


# Class representing an algorithm under test.
class IsqrtAlgorithm:
    def __init__(self, function, min=0, max=None):
        self.function = function
        self.min = min
        self.max = max

    def __call__(self, n):
        return self.function(n)

    def __repr__(self):
        return self.function.__module__


ISQRT_ALGORITHMS = [
    IsqrtAlgorithm(isqrt_heron_direct.isqrt, min=1),
    IsqrtAlgorithm(isqrt_heron_improved.isqrt, min=1),
    IsqrtAlgorithm(isqrt_recursive.isqrt, min=1),
    IsqrtAlgorithm(isqrt_iterative.isqrt, min=1),
    IsqrtAlgorithm(isqrt_32bit.isqrt, max=2**32-1),
    IsqrtAlgorithm(isqrt_64bit.isqrt, max=2**64-1),
    IsqrtAlgorithm(isqrt_accelerated.isqrt, min=1),
]


class TestIsqrt(unittest.TestCase):
    def test_small_integers(self):
        for algorithm in ISQRT_ALGORITHMS:
            for n in range(10**5):
                with self.subTest(algorithm=algorithm, n=n):
                    self.checkIsqrt(algorithm, n)

    def test_near_squares(self):
        for algorithm in ISQRT_ALGORITHMS:
            for a in range(1, 10**5):
                with self.subTest(algorithm=algorithm, a=a):
                    self.checkIsqrt(algorithm, a*a)
                    self.checkIsqrt(algorithm, a*a + 2*a)

    def test_near_midpoints(self):
        for algorithm in ISQRT_ALGORITHMS:
            for a in range(1, 10**5):
                with self.subTest(algorithm=algorithm, a=a):
                    self.checkIsqrt(algorithm, a*a + a)
                    self.checkIsqrt(algorithm, a*a + a + 1)

    def test_near_power_of_two_boundaries(self):
        test_values = []

        for e in [31, 32, 52, 53, 54, 105, 106, 107, 108, 159, 211, 212]:
            for a in range(2**e-10, 2**e+11):
                for d in range(-5, 6):
                    test_values.append(a*a+d)

        for algorithm in ISQRT_ALGORITHMS:
            for n in test_values:
                with self.subTest(algorithm=algorithm, n=n):
                    self.checkIsqrt(algorithm, n)

    def test_large_random(self):
        random_state = random.Random(x=24680)

        for algorithm in ISQRT_ALGORITHMS:
            for bit_length in range(512, 2048):
                n = random_state.getrandbits(bit_length)
                with self.subTest(algorithm=algorithm, n=n):
                    self.checkIsqrt(algorithm, n)

    def checkIsqrt(self, algorithm, n):
        if n < algorithm.min:
            return
        if algorithm.max is not None and n > algorithm.max:
            return
        a = algorithm(n)
        self.assertLessEqual(a*a, n)
        self.assertLess(n, (a+1)*(a+1))
