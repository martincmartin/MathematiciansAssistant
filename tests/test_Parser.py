import unittest

# To run tests:
#
# coverage run --branch test_Parser.py && coverage report --show-missing

# To run a single test:
#
# python3 test_Parser.py TestParser.test_malformed

# To enter the debugger when a test fails, uncomment this line:
# unittest.TestCase.run = lambda self, *args, **kw: unittest.TestCase.debug(self)
# python3 -m pdb -c continue test_Parser.py

from Expression import var, and_, or_, not_, implies, equal, in_, iff, \
    matrix_literal, list_literal, num

import Parser
# from DeductionHelpers import *
import tokenize

# from pprint import pprint

P = var("P")
Q = var("Q")
R = var("R")
A = var("A")
B = var("B")
M = var("M")

a = var("a")
b = var("b")
c = var("c")
d = var("d")

p = var("p")
q = var("q")
r = var("r")
s = var("s")


def ex(string):
    return Parser.parse(string)


class TestParser(unittest.TestCase):

    def test_malformed(self):
        with self.assertRaises(SyntaxError):
            ex("+")

    def test_malformed2(self):
        with self.assertRaises(SyntaxError):
            ex("P Q")

    def test_malformed3(self):
        with self.assertRaises(tokenize.TokenError):
            ex("( P")

    def test_mult(self):
        self.assertEqual(ex("P*Q"), P * Q)

    def test_mult2(self):
        self.assertEqual(ex("P*Q*R"), (P * Q) * R)

    def test_mult3(self):
        self.assertEqual(ex("P*(Q*R)"), P * (Q * R))

    def test_mult4(self):
        self.assertEqual(ex("(P*Q)*R"), (P * Q) * R)

    def test_add_mult(self):
        self.assertEqual(ex("P + Q*R"), P + Q * R)

    def test_add_mult2(self):
        self.assertEqual(ex("P * Q+R"), P * Q + R)

    def test_add_mult3(self):
        self.assertEqual(ex("(P + Q) * R"), (P + Q) * R)

    def test_add_mult4(self):
        self.assertEqual(ex("P * (Q + R)"), P * (Q + R))

    def test_compare(self):
        self.assertEqual(
            ex("R * (P + Q) == R * P + R * Q"),
            equal(R * (P + Q), R * P + R * Q),
        )

    def test_in(self):
        self.assertEqual(ex("P + Q in B"), in_(P + Q, B))

    def test_not(self):
        self.assertEqual(ex("not P == Q"), not_(equal(P, Q)))

    def test_not2(self):
        self.assertEqual(ex("not P and Q"), and_(not_(P), Q))

    def test_not3(self):
        self.assertEqual(ex("P or not Q"), or_(P, not_(Q)))

    def test_implies(self):
        self.assertEqual(
            ex("not P or Q ==> A and B"), implies(or_(not_(P), Q), and_(A, B))
        )

    def test_iff(self):
        self.assertEqual(
            ex("not P or Q <==> (P ==> Q)"), iff(or_(not_(P), Q), implies(P, Q))
        )

    def test_implies_precedence(self):
        self.assertEqual(
            ex("P ==> Q and not Q ==> not P"),
            implies(implies(P, and_(Q, not_(Q))), not_(P)),
        )

    def test_implies_precedence2(self):
        self.assertEqual(
            ex("(P ==> Q) and not Q ==> not P"),
            implies(and_(implies(P, Q), not_(Q)), not_(P)),
        )

    def test_implies_precedence3(self):
        self.assertEqual(
            ex("((P ==> Q) and not Q) ==> not P"),
            implies(and_(implies(P, Q), not_(Q)), not_(P)),
        )

    # # Python syntax for lists.
    # def test_list(self):
    #     self.assertEqual(
    #         ex('[P, P ==> Q, P * R]'),
    #         list_(P, implies(P, Q), multiply(P, R)))

    def test_matrix(self):
        self.assertEqual(
            ex("[P Q; Q R]"),
            matrix_literal(list_literal(P, Q), list_literal(Q, R)),
        )

        self.assertEqual(
            ex("M == [1 1; 0 1]"),
            equal(
                M,
                matrix_literal(
                    list_literal(num(1), num(1)), list_literal(num(0), num(1))
                ),
            ),
        )

    def test_number_literal(self):
        self.assertEqual(ex("0"), num(0))
        self.assertEqual(ex("1"), num(1))
        self.assertEqual(ex("954"), num(954))

        # Apparently, Python parses "054" as two NUMBERs, 0 and 54.  Strange.
        # self.assertEqual(ex('054'), num(54))

        # -5 would be parsed as a unary minus applied to num(5), but we don't
        # have unary minus yet.
        # self.assertEqual(ex('-5'), minus(num(5)))



if __name__ == "__main__":  # pragma: no cover
    unittest.main()
