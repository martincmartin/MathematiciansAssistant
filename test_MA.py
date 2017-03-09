import unittest

# To enter the debugger when a test fails, uncomment this line:
# unittest.TestCase.run = lambda self, *args, **kw: unittest.TestCase.debug(self)
# python3 -m pdb -c continue test_MA.py

from MA import *

P = var('P')
Q = var('Q')
A = var('A')
B = var('B')


class TestMatch(unittest.TestCase):
    def test_node(self):
        self.assertEqual(
            match([P], P, P + Q),
            {P: (P + Q)})

    def test_sum(self):
        self.assertEqual(
            match([P], P + B, Q + B),
            {P: Q})

    def test_different_root(self):
        self.assertIsNone(
            match([], P + Q, P * Q))

    def test_different_len(self):
        self.assertIsNone(
            match([], P + Q, sum(P, Q, A)))

    def test_simple(self):
        self.assertEqual(
            match([P], in_(P, B), in_(P + Q, B)),
            {P: (P + Q)})

    def test_dummy_appears_twice(self):
        self.assertEqual(
            match([P], in_(P, P), in_(P + Q, P + Q)),
            {P: (P + Q)})

    def test_dummy_appears_twice2(self):
        self.assertIsNone(
            match([P], in_(P, P), in_(P + Q, P + B)))

    def test_two_dimmies(self):
        self.assertEqual(
            match([P, Q], P + Q, A + B),
            {P: A, Q: B})


if __name__ == '__main__':
    unittest.main()
