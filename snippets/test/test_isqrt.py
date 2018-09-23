import unittest

from snippets.isqrt import (
    isqrt,
    isqrt_bytes,
    isqrt_pure,
    isqrt_recursive,
    isqrt_recursive_pure,
)


class TestIsqrtMixin(object):
    """
    Common tests for all isqrt implementations.
    """
    def test_negative(self):
        with self.assertRaises(ValueError):
            self.isqrt(-3)
        with self.assertRaises(ValueError):
            self.isqrt(-1)

    def test_nonnegative(self):
        for n in range(256):
            a = self.isqrt(n)
            self.assertIsInstance(a, int)
            self.assertLessEqual(a**2, n)
            self.assertLess(n, (a + 1)**2)

    def test_large_n(self):
        large = list(range(10**100 - 100, 10**100 + 100))
        large.extend(range(10**1000 - 100, 10**1000 + 100))
        for n in large:
            a = self.isqrt(n)
            self.assertIsInstance(a, int)
            self.assertLessEqual(a**2, n)
            self.assertLess(n, (a + 1)**2)

    def test_type(self):
        self.assertIsInstance(self.isqrt(False), int)
        self.assertIsInstance(self.isqrt(True), int)


class TestISqrt(TestIsqrtMixin, unittest.TestCase):
    def setUp(self):
        self.isqrt = isqrt


class TestISqrtBytes(TestIsqrtMixin, unittest.TestCase):
    def setUp(self):
        self.isqrt = isqrt_bytes


class TestISqrtPure(TestIsqrtMixin, unittest.TestCase):
    def setUp(self):
        self.isqrt = isqrt_pure


class TestISqrtRecursive(TestIsqrtMixin, unittest.TestCase):
    def setUp(self):
        self.isqrt = isqrt_recursive


class TestISqrtRecursivePure(TestIsqrtMixin, unittest.TestCase):
    def setUp(self):
        self.isqrt = isqrt_recursive_pure
