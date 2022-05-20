# Run using:
# python3 -m unittest tests/test_DeductionCalcMode.py
import unittest
import MatchAndSubstitute

import Parser

from Expression import (
    sum_simplifier,
    negative,
    negative_simplifier,
    equal,
    Expression,
    Negative,
    forall,
    var,
    num,
    ExpressionType,
    Sum,
)

from DeductionCalcMode import (
    DeductionCalcMode,
    DistanceExprAndParent,
    has_subexpression,
    parts,
    missing,
    try_forall_elimination,
)

OBJECT = ExpressionType.OBJECT
NUMBER_LITERAL = ExpressionType.NUMBER_LITERAL

x = var("x", OBJECT)

xl = var("x", NUMBER_LITERAL)
yl = var("y", NUMBER_LITERAL)


a = var("a", OBJECT)
b = var("b", OBJECT)
c = var("c", OBJECT)

FORWARD = MatchAndSubstitute.Direction.FORWARD


def ex(string: str) -> Expression:
    return Parser.parse(string)


class TestParts(unittest.TestCase):
    def test_var(self) -> None:
        self.assertEqual({x: 1}, parts(x))

    def test_number_literal(self) -> None:
        self.assertEqual({num(5): 1}, parts(ex("5")))

    def test_sum_literals(self) -> None:
        self.assertEqual({num(3): 1, num(5): 1, Sum(): 1}, parts(ex("3 + 5")))

    def test_x_plus_minus(self) -> None:
        self.assertEqual(
            {num(3): 2, x: 1, Sum(): 2, Negative(): 1}, parts(ex("(x + 3) + -3"))
        )
        self.assertEqual(
            {num(3): 2, x: 1, Sum(): 2, Negative(): 1}, parts(ex("x + (3 + -3)"))
        )


class TestMissing(unittest.TestCase):
    def test_x(self) -> None:
        self.assertEqual(missing(x, ex("x + 3")), {Sum(): 1, num(3): 1})

    def test_x_plus_zero(self) -> None:
        self.assertEqual(missing(ex("x + 0"), ex("x + 3")), {num(3): 1})

    def test_x_plus_minus_three(self) -> None:
        self.assertEqual(missing(ex("(x + 3) + -3"), ex("x + 3")), {})

    def test_x_plus_minus_three_2(self) -> None:
        self.assertEqual(missing(ex("x + (3 + -3)"), ex("x + 3")), {})


class TestHasSubexpression(unittest.TestCase):
    def test_var(self) -> None:
        self.assertTrue(has_subexpression(x, x))
        self.assertTrue(has_subexpression(x + yl, x))
        self.assertTrue(has_subexpression(x + yl, yl))

        self.assertFalse(has_subexpression(x, yl))
        self.assertFalse(has_subexpression(ex("x * x"), yl))

    def test_number_literal(self) -> None:
        self.assertTrue(has_subexpression(ex("3 + 5"), num(3)))
        self.assertTrue(has_subexpression(ex("3 + 5"), num(5)))
        self.assertFalse(has_subexpression(ex("3 + 5"), num(8)))

        self.assertTrue(has_subexpression(num(3), num(3)))
        self.assertFalse(has_subexpression(num(3), num(5)))

    def test_x_plus_3(self) -> None:
        self.assertTrue(has_subexpression(ex("x + 3"), ex("x + 3")))
        self.assertFalse(has_subexpression(ex("x + 5"), ex("x + 3")))
        self.assertTrue(has_subexpression(ex("x + 3 - 3"), ex("x + 3")))
        self.assertTrue(has_subexpression(ex("x + 3 + -3"), ex("x + 3")))
        self.assertFalse(has_subexpression(ex("x + (3 - 3)"), ex("x + 3")))
        self.assertFalse(has_subexpression(ex("x + (3 + -3)"), ex("x + 3")))


class TestForallElimination(unittest.TestCase):
    def test_not_forall(self) -> None:
        self.assertEqual(try_forall_elimination(ex("2 + 3"), num(2)), set())

    def test_simple(self) -> None:
        self.assertEqual(
            try_forall_elimination(forall(a, ex("x + (a + -a)")), num(3)),
            {ex("x + (3 + -3)")},
        )

    def test_multi(self) -> None:
        self.assertEqual(
            try_forall_elimination(forall([a, x], ex("x + (a + -a)")), num(3)),
            {forall(x, ex("x + (3 + -3)")), forall(a, ex("3 + (a + -a)"))},
        )


class TestTryRule(unittest.TestCase):
    def test_first_step(self) -> None:
        self.assertEqual(
            [x, x + num(0)],
            DeductionCalcMode(ex("x + 3"), 0).try_rule(
                forall(x, ex("x + 0 == x")), DistanceExprAndParent(x, None, 5)
            ),
        )

    def test_second_step(self) -> None:
        # Convert x + 0 to x + (3 + -3).
        desired_subexpression = ex("x + 3")
        start_expression = ex("x + 0")

        still_need = missing(start_expression, desired_subexpression)
        self.assertEqual(still_need, {num(3): 1})

        rule = forall(a, ex("a + -a == 0"))

        # Now need to apply 0 -> a + -a.  What's the motivation for that?  Just
        # that there isn't a "3" in any expression in the context, so we need to
        # introduce a forall to eliminate it?  Or we can always fall back on
        # brute search: try everything in the context, notice a forall is
        # introduced, then try forall elimination.
        exprs = MatchAndSubstitute.try_rule(rule, start_expression, FORWARD, True)
        self.assertEqual(exprs, {forall(a, ex("x + (a + -a)"))})

        next_expression = next(iter(exprs))
        self.assertEqual(next_expression, forall(a, ex("x + (a + -a)")))

        exprs = try_forall_elimination(next_expression, num(3))
        self.assertEqual(exprs, {ex("x + (3 + -3)")})
        self.assertFalse(has_subexpression(next(iter(exprs)), desired_subexpression))

    def test_third_step(self) -> None:
        # Convert x + (3 + -3) into (x + 3) + -3.
        desired_subexpression = ex("x + 3")
        start_expression = ex("x + (3 + -3)")

        associative = forall([a, b, c], ex("(a + b) + c == a + (b + c)"))

        exprs = MatchAndSubstitute.try_rule(associative, start_expression, FORWARD)

        self.assertEqual(exprs, {ex("(x + 3) + -3")})
        self.assertTrue(has_subexpression(next(iter(exprs)), desired_subexpression))

    def test_fourth_step(self) -> None:
        # Convert (x + 3) + -3 into 5 + -3.
        start_expression = ex("(x + 3) + -3")

        given = ex("x + 3 == 5")

        exprs = MatchAndSubstitute.try_rule(given, start_expression, FORWARD)
        self.assertEqual(exprs, {ex("5 + -3")})

        negative_simplifier_rule = forall(
            xl, equal(negative(xl), negative_simplifier(xl))
        )
        self.assertEqual(
            MatchAndSubstitute.try_rule(
                negative_simplifier_rule, ex("5 + -3"), FORWARD
            ),
            {num(5) + num(-3)},
        )

        sum_simplifier_rule = forall((xl, yl), equal(xl + yl, sum_simplifier(xl, yl)))
        self.assertEqual(
            MatchAndSubstitute.try_rule(sum_simplifier_rule, num(5) + num(-3), FORWARD),
            {num(2)},
        )
