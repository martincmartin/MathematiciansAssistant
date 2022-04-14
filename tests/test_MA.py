import unittest

# To run tests:
#
# coverage run --branch test_MA.py && coverage report --show-missing

# To run a single test:
#
# python3 test_MA.py TestTryRule.test_matrix_mult

# To enter the debugger when a test fails, uncomment this line:
# unittest.TestCase.run = lambda self, *args, **kw: unittest.TestCase.debug(self)
# python3 -m pdb -c continue test_MA.py

from Expression import var, ExpressionType
import Parser
from DeductionOrig import path_length

# from pprint import pprint

# Save some typing
OBJECT = ExpressionType.OBJECT


P = var("P", OBJECT)
Q = var("Q", OBJECT)
R = var("R", OBJECT)
A = var("A", OBJECT)
B = var("B", OBJECT)
M = var("M", OBJECT)

# a = var("a")
# b = var("b")
# c = var("c")
# d = var("d")

# p = var("p")
# q = var("q")
# r = var("r")
# s = var("s")


def ex(string: str):
    return Parser.parse(string)


class TestPathLength(unittest.TestCase):
    # Modifies inputs (sorts them).
    def assert_path_length_result(self, actual, expected):
        # Make sure its in order by the first argument.
        for i in range(len(actual) - 1):
            self.assertLessEqual(actual[i][0], actual[i + 1][0])

        self.assertEqual(
            actual.sort(key=lambda x: (x[0], id(x))),
            expected.sort(key=lambda x: (x[0], id(x))),
        )

    def test_simple(self):
        self.assert_path_length_result(
            path_length(P, M, ex("(P + Q) * M == M * (P + Q)")),
            [(3, P, M), (3, P, M), (5, P, M), (5, P, M)],
        )

        #         ===
        #     *         *
        #   +   M     M   +
        # P   Q         P   Q

    def test_simple2(self):
        self.assert_path_length_result(
            path_length(M, P, ex("(P + Q) * M == M * (P + Q)")),
            [(3, M, P), (3, M, P), (5, M, P), (5, M, P)],
        )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
