import unittest

import Parser

from Expression import (
    ExpressionType,
    Expression,
    forall,
    exists,
    var,
    list_literal,
    num,
    in_,
    and_,
    matrix_literal,
    sum_,
    implies,
)

OBJECT = ExpressionType.OBJECT
PROPOSITION = ExpressionType.PROPOSITION

A = var("A", OBJECT)
B = var("B", OBJECT)
M = var("M", OBJECT)
P = var("P", PROPOSITION)
Q = var("Q", PROPOSITION)
R = var("R", OBJECT)

a = var("a", OBJECT)
b = var("b", OBJECT)
c = var("c", OBJECT)
d = var("d", OBJECT)


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
        self.assertEqual(
            r"\forall{P: PROPOSITION}(P ==> P)",
            repr(forall(P, ex("P ==> P"))),
        )

        self.assertEqual(
            r"\forall{a: OBJECT, b: OBJECT}(a + b == b + a)",
            repr(forall((a, b), ex("a + b == b + a"))),
        )

    def test_exists(self):
        self.assertEqual(
            r"\exists{A: OBJECT}(A + A == A)", repr(exists(A, ex("A + A == A")))
        )

    def test_in(self):
        self.assertEqual(repr(in_(A, B)), r"A \in B")

    def test_number_literal(self):
        self.assertEqual(repr(num(15)), "15")

    def test_list_literal(self):
        self.assertEqual(repr(list_literal(num(5), a, b)), "[5, a, b]")

    def test_matrix_literal(self):
        self.assertEqual(
            repr(
                matrix_literal(list_literal(num(5), a, b), list_literal(num(0), c, d))
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
        self.assertEqual(forall(P, ex("P or Q ==> Q")).free_variables(set()), {Q})

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
        self.assertEqual(forall(A, ex("A * M == M * A")).bound_variables(), {"A"})

    def test_multiple_with_same_name(self) -> None:
        self.assertEqual(
            and_(
                forall(var("P", OBJECT), ex("P + P == P")),
                forall(var("P", PROPOSITION), ex("P or not P")),
            ).bound_variables(),
            {"P"},
        )


class TestFreeVariables(unittest.TestCase):
    def test_basic(self) -> None:
        self.assertEqual(
            {a, b},
            ex("a + b == b + a").free_variables(frozenset()),
        )

    def test_quantifier(self) -> None:
        self.assertEqual(
            {a}, forall(b, ex("a + b == b + a")).free_variables(frozenset())
        )

    def test_shadow(self) -> None:
        self.assertEqual(
            {P},
            and_(P, forall(P, ex("P or not P"))).free_variables(frozenset()),
        )


class TestVariables(unittest.TestCase):
    def test_basic(self) -> None:
        # Only non-empty on quantifiers.
        self.assertEqual(and_(P, Q).get_variables({}), {})

        self.assertEqual(and_(P, forall(Q, ex("Q and Q"))).get_variables({}), {})

        self.assertEqual(forall(P, ex("P ==> P")).get_variables({}), {"P": P})

        self.assertEqual(
            forall((P, Q), ex("P ==> Q")).get_variables({}), {"P": P, "Q": Q}
        )

        self.assertEqual(
            forall(P, forall(Q, ex("P ==> Q"))).get_variables({}), {"P": P}
        )


if __name__ == "__main__":
    # with typeguard.TypeChecker(["Parser", "Expression"]):
    unittest.main()
