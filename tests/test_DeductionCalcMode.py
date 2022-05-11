# Run using:
# python3 -m unittest tests/test_DeductionCalcMode.py
import unittest

import Parser

from Expression import Expression, Negative, forall, var, num, ExpressionType, Sum

from DeductionCalcMode import (
    DeductionCalcMode,
    DistanceExprAndParent,
    has_subexpression,
    parts,
    missing,
)

OBJECT = ExpressionType.OBJECT
NUMBER_LITERAL = ExpressionType.NUMBER_LITERAL

x = var("x", OBJECT)
y = var("y", NUMBER_LITERAL)


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
        self.assertTrue(has_subexpression(x + y, x))
        self.assertTrue(has_subexpression(x + y, y))

        self.assertFalse(has_subexpression(x, y))
        self.assertFalse(has_subexpression(ex("x * x"), y))

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


class TestTryRule(unittest.TestCase):
    def test_first_step(self) -> None:
        self.assertEqual(
            [x, x + num(0)],
            DeductionCalcMode(ex("x + 3"), 0).try_rule(
                forall(x, ex("x + 0 == x")), DistanceExprAndParent(x, None, 5)
            ),
        )

    def test_more_steps(self) -> None:
        desired_subexpression = ex("x + 3")
        deduction = DeductionCalcMode(desired_subexpression, 0)

        identity = forall(x, ex("x + 0 == x"))

        nodes_needed = missing(x, desired_subexpression)

        start = DistanceExprAndParent(x, None, sum(nodes_needed.values()))

        deduction.try_rule(identity, start)

        # Now we need to turn 0 into 3 + -3.  I don't think this can be done by
        # treating the distance function as a black box, as we'll never get the
        # idea to try substituting 3 into a + -a that way.  So we need to know
        # specifically that we're looking for a 3.  In other words, we don't
        # want to think of the distance as a number, more as a multiset of
        # missing Nodes, implemented as dict from Node to count.
