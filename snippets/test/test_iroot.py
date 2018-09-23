import unittest

from snippets.icbrt import icbrt
from snippets.iroot import iroot
from snippets.isqrt import isqrt


class TestIroot(unittest.TestCase):
    def test_invalid_inputs(self):
        with self.assertRaises(ValueError):
            iroot(-1, 5)
        with self.assertRaises(ValueError):
            iroot(4, 0)
        with self.assertRaises(ValueError):
            iroot(-27, -3)
        with self.assertRaises(ValueError):
            iroot(0, 0)

    def test_first_root(self):
        for n in range(1000):
            self.assertEqual(iroot(n, 1), n)

    def test_matches_isqrt(self):
        for n in range(1000):
            self.assertEqual(iroot(n, 2), isqrt(n))

    def test_matches_icbrt(self):
        for n in range(1000):
            self.assertEqual(iroot(n, 3), icbrt(n))

    def test_fourth_root(self):
        for n in range(1000):
            k = iroot(n, 4)
            self.assertLessEqual(k**4, n)
            self.assertLess(n, (k + 1)**4)

    def test_large_root(self):
        self.assertEqual(iroot(2**10000, 10000), 2)
        self.assertEqual(iroot(2**10000 - 1, 10000), 1)
