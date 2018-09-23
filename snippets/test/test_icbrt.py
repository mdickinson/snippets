import unittest

from snippets.icbrt import icbrt, icbrt_pure


class TestIcbrtMixin(object):
    def test_negative(self):
        with self.assertRaises(ValueError):
            self.icbrt(-3)
        with self.assertRaises(ValueError):
            self.icbrt(-1)

    def test_nonnegative(self):
        for n in range(1000):
            a = self.icbrt(n)
            self.assertIsInstance(a, int)
            self.assertLessEqual(a**3, n)
            self.assertLess(n, (a + 1)**3)

    def test_output_type(self):
        self.assertIsInstance(self.icbrt(False), int)
        self.assertIsInstance(self.icbrt(True), int)

    def test_huge(self):
        for n in range(10**300 - 100, 10**300 + 100):
            a = self.icbrt(n)
            self.assertIsInstance(a, int)
            self.assertLessEqual(a**3, n)
            self.assertLess(n, (a + 1)**3)

    def test_type(self):
        self.assertIsInstance(self.icbrt(False), int)
        self.assertIsInstance(self.icbrt(True), int)


class TestICbrt(TestIcbrtMixin, unittest.TestCase):
    def setUp(self):
        self.icbrt = icbrt


class TestICbrtPure(TestIcbrtMixin, unittest.TestCase):
    def setUp(self):
        self.icbrt = icbrt_pure
