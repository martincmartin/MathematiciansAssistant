import unittest
import Parser

from Expression import (
    Expression,
    forall,
    exists,
    var,
    list_literal,
    num,
    in_,
    matrix_literal,
    sum_,
    implies,
)

import typeguard

A = var("A")
B = var("B")
M = var("M")
P = var("P")
Q = var("Q")
R = var("R")

a = var("a")
b = var("b")
c = var("c")
d = var("d")


def ex(string: str) -> Expression:
    return Parser.parse(string)


class TestRepr(unittest.TestCase):

    def canonical(self, expr: str) -> None:
        assert isinstance(expr, str)
        self.assertEqual(repr(ex(expr)), expr)

    def test_mult_add(self) -> None:
        self.canonical("P * Q + R")

        self.canonical("P * (Q + R)")

    def test_not(self) -> None:
        self.canonical("not P")

    def test_not2(self):
        self.canonical("not (P and Q)")

    def test_forall(self):
        self.assertEqual(repr(forall(P, ex("P ==> P"))), r"\forall{P}(P ==> P)")

        self.assertEqual(
            repr(forall((P, Q), ex("P + Q == Q + P"))),
            r"\forall{P, Q}(P + Q == Q + P)",
        )

    def test_exists(self):
        self.assertEqual(
            repr(exists(A, ex("A + A == A"))), r"\exists{A}(A + A == A)"
        )

    def test_in(self):
        self.assertEqual(repr(in_(P, B)), r"P \in B")

    def test_number_literal(self):
        self.assertEqual(repr(num(15)), "15")

    def test_list_literal(self):
        self.assertEqual(repr(list_literal(num(5), a, b)), "[5, a, b]")

    def test_matrix_literal(self):
        self.assertEqual(
            repr(
                matrix_literal(
                    list_literal(num(5), a, b), list_literal(num(0), c, d)
                )
            ),
            "[5  a  b; 0  c  d]",
        )

    def test_matrix_literal_nonstandard(self) -> None:
        self.assertEqual(
            repr(
                matrix_literal(
                    list_literal(num(5), a, b),
                    sum_(num(3), list_literal(num(0), c, d)),
                )
            ),
            "[[5, a, b], 3 + [0, c, d]]",
        )

    def test_num_canonical(self) -> None:
        self.canonical("23")

    def test_matrix_canonical(self) -> None:
        self.canonical("[5  a  b; 0  c  d]")

    # We don't parse this yet.
    # def test_matrix_canonical_nonstandard(self):
    #     self.canonical('[[5, a, b], 3 + [0, c, d]]')


class TestFreeVars(unittest.TestCase):

    def test_basic(self) -> None:
        self.assertEqual(ex("a + b").free_variables(set()), {a, b})

    def test_quantifier(self) -> None:
        self.assertEqual(
            forall(P, ex("P or Q ==> Q")).free_variables(set()), {Q}
        )

    def test_shadow_free(self) -> None:
        self.assertEqual(
            implies(P, forall(P, ex("P or not P"))).free_variables(set()), {P}
        )

    # I've decided to outlaw shadowing, for the same reason we don't allow
    # it in C++ code: it can confuse the human reader.
    #
    # def test_shadow_bound(self) -> None:
    #     self.assertEqual(
    #         forall(P, implies(P, forall(P, ex("P or not P")))).free_variables(
    #             set()
    #         ),
    #         set(),
    #     )

class TestBoundVariables(unittest.TestCase):

    def test_basic(self) -> None:
        self.assertEqual(forall(P, ex("P * M == M * P")).bound_variables(),
                         {P})

if __name__ == "__main__":
    with typeguard.TypeChecker(["Parser", "Expression"]):
        unittest.main()
