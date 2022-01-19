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

from Expression import (
    var,
    and_,
    or_,
    not_,
    implies,
    equal,
    in_,
    iff,
    matrix_literal,
    list_literal,
    num,
    Expression
    ExpressionType,
)

import Parser

# from DeductionHelpers import *
import tokenize

# from pprint import pprint

OBJECT = ExpressionType.OBJECT
PROPOSITION = ExpressionType.PROPOSITION

P = var("P", PROPOSITION)
Q = var("Q", PROPOSITION)
R = var("R", PROPOSITION)
S = var("S", PROPOSITION)

A = var("A", OBJECT)
B = var("B", OBJECT)
C = var("C", OBJECT)

M = var("M", OBJECT)

a = var("a", OBJECT)
b = var("b", OBJECT)
c = var("c", OBJECT)
d = var("d", OBJECT)

p = var("p", OBJECT)
q = var("q", OBJECT)
r = var("r", OBJECT)
s = var("s", OBJECT)


def ex(string: str) -> Expression:
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
        self.assertEqual(ex("A*B"), A * B)

    def test_mult2(self):
        self.assertEqual(ex("A*B*C"), (A * B) * C)

    def test_mult3(self):
        self.assertEqual(ex("A*(B*C)"), A * (B * C))

    def test_mult4(self):
        self.assertEqual(ex("(A*B)*C"), (A * B) * C)

    def test_add_mult(self):
        self.assertEqual(ex("A + B*C"), A + B * C)

    def test_add_mult2(self):
        self.assertEqual(ex("A * B+C"), A * B + C)

    def test_add_mult3(self):
        self.assertEqual(ex("(A + B) * C"), (A + B) * C)

    def test_add_mult4(self):
        self.assertEqual(ex("A * (B + C)"), A * (B + C))

    def test_compare(self):
        self.assertEqual(
            ex("C * (A + B) == C * A + C * B"),
            equal(C * (A + B), C * A + C * B),
        )

    def test_in(self):
        self.assertEqual(ex("A + B in C"), in_(A + B, C))

    def test_not(self):
        self.assertEqual(ex("not P <==> Q"), iff(not_(P), Q))

    def test_not2(self):
        self.assertEqual(ex("not P and Q"), and_(not_(P), Q))

    def test_not3(self):
        self.assertEqual(ex("P or not Q"), or_(P, not_(Q)))

    def test_implies(self):
        self.assertEqual(
            ex("not P or Q ==> R and S"), implies(or_(not_(P), Q), and_(R, S))
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
            ex("[A B; B C]"),
            matrix_literal(list_literal(A, B), list_literal(B, C)),
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
