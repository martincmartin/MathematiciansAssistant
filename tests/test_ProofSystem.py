import unittest

import Parser
from Expression import var, ExpressionType
from ProofSystem import ExprAndParent, Exprs, collect_path


OBJECT = ExpressionType.OBJECT
a = var("a", OBJECT)
b = var("b", OBJECT)
c = var("c", OBJECT)


def ex(string: str):
    return Parser.parse(string)


class TestCalcMode(unittest.TestCase):
    def test_blah(self):
        og = ExprAndParent(ex("(x + 7) + -7"), None)
        exprs = Exprs([og])

        second = ExprAndParent(ex("x + (7 + -7)"), og)
        self.assertFalse(second.expr in exprs)
        exprs.add(second)
        self.assertTrue(second.expr in exprs)

        third = ExprAndParent(ex("x + 0"), second)
        self.assertFalse(third.expr in exprs)
        exprs.add(third)
        self.assertTrue(og.expr in exprs)
        self.assertTrue(second.expr in exprs)
        self.assertTrue(third.expr in exprs)

        fourth = ExprAndParent(var("x", OBJECT), third)

        path = list(reversed(collect_path(fourth)))
        self.assertEqual(path, [og.expr, second.expr, third.expr, fourth.expr])
