import unittest

from Expression import var, forall, equal, sum_simplifier, ExpressionType, Expression
from MatchAndSubstitute import try_rule, Direction
import Parser

OBJECT = ExpressionType.OBJECT
NUMBER_LITERAL = ExpressionType.NUMBER_LITERAL

x = var("x", OBJECT)
y = var("y", OBJECT)

xl = var("x", NUMBER_LITERAL)
yl = var("y", NUMBER_LITERAL)

sum_simplifier_rule = forall((xl, yl), equal(xl + yl, sum_simplifier(xl, yl)))


def ex(string: str) -> Expression:
    return Parser.parse(string)


# **********  Field axioms

# ***** Identities
additive_identity = forall(x, ex("x + 0 == x"))
multiplicative_identity = forall(x, ex("x * 1 == x"))


class TestSimplify(unittest.TestCase):
    def test_add_zero(self):
        self.assertEqual(
            {x},
            try_rule(
                additive_identity,
                ex("x + 0"),
                Direction.FORWARD,
            ),
        )


if __name__ == "__main__":
    unittest.main()
