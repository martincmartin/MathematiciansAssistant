import unittest

from MatchAndSubstitute import match, is_instance, is_rule, try_rule, Direction
import Parser
from Expression import var, sum_, num, forall
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

p = var("p")
q = var("q")
r = var("r")
s = var("s")


def ex(string):
    return Parser.parse(string)


class TestMatch(unittest.TestCase):

    def test_node(self):
        self.assertEqual(match({P}, P, P + Q), {P: (P + Q)})

    def test_sum(self):
        self.assertEqual(match({P}, P + B, Q + B), {P: Q})

    def test_different_root(self):
        self.assertIsNone(match(set(), P + Q, P * Q))

    def test_different_len(self):
        self.assertIsNone(match(set(), P + Q, sum_(P, Q, A)))

    def test_simple(self):
        self.assertEqual(
            match({P}, ex("P in B"), ex("P + Q in B")), {P: (P + Q)}
        )

    def test_dummy_appears_twice(self):
        self.assertEqual(
            match({P}, ex("P in P"), ex("P + Q in P + Q")), {P: (P + Q)}
        )

    def test_dummy_appears_twice2(self):
        self.assertIsNone(match({P}, ex("P in P"), ex("P + Q in P + B")))

    def test_two_dummies(self):
        self.assertEqual(match({P, Q}, P + Q, A + B), {P: A, Q: B})

    def test_number_literal(self):
        self.assertEqual(match({a}, a, num(1)), {a: num(1)})

    def test_matrix_literal(self):
        self.assertEqual(
            match({a, b, c, d}, ex("[a b; c d]"), ex("[1 2; 3 4]")),
            {a: num(1), b: num(2), c: num(3), d: num(4)},
        )


class TestIsInstance(unittest.TestCase):

    def test_reflexivity_of_equals(self):
        self.assertEqual(
            is_instance(
                ex("M * P + M * Q == M * P + M * Q"),
                forall(A, ex("A == A")),
                set(),
            ),
            {A: ex("M * P + M * Q")},
        )

    def test_distributed_law(self):
        self.assertEqual(
            is_instance(
                ex("(P + Q) * M == P * M + Q * M"),
                forall((A, B, M), ex("(A + B) * M == A * M + B * M")),
            ),
            {A: P, B: Q, M: M},
        )


class TestIsRule(unittest.TestCase):

    def test_equals(self):
        self.assertTrue(is_rule(ex("P * M == M * P")))

    def test_equivalent(self):
        self.assertTrue(is_rule(ex("A and B <==> B and A")))

    def test_implies(self):
        self.assertTrue(is_rule(ex("(P and P ==> Q) ==> Q")))

    def test_forall_equals(self):
        self.assertTrue(is_rule(forall((P, M), ex("P * M == M * P"))))


class TestTryRule(unittest.TestCase):

    def test_doesnt_match(self):
        self.assertEqual(
            try_rule(
                forall((P, Q, R), ex("(P + Q) * R == P * R + Q * R")),
                ex("P + Q in B"),
                Direction.BACKWARD,
            ),
            set(),
        )

    def test_modus_tollens(self):
        self.assertEqual(
            try_rule(
                forall((P, Q), ex("((P ==> Q) and not Q) ==> not P")),
                ex("not B"),
                Direction.BACKWARD,
            ),
            {ex("(B ==> Q) and not Q")},
        )
        # dummies: (P, Q).
        # rule: ((P ==> Q) and not Q) ==> not P
        # target: not B

        # dummies: (P, Q).
        # to_match: not P
        # replacement: (P ==> Q) and not Q
        # target: not B

    def test_modus_ponens(self):
        self.assertEqual(
            try_rule(
                forall((P, Q), ex("((P ==> Q) and P) ==> Q")),
                ex("(A ==> B) and A"),
                Direction.FORWARD,
            ),
            {ex("B")},
        )

    def test_definition_of_set(self):
        self.assertEqual(
            try_rule(
                forall(P, ex("P in B <==> P * M == M * P")),
                ex("P + Q in B"),
                Direction.BACKWARD,
            ),
            {ex("(P + Q) * M == M * (P + Q)")},
        )

    def test_distribute_right(self):
        self.assertEqual(
            try_rule(
                forall((A, B, R), ex("(A + B) * R == A * R + B * R")),
                ex("(P + Q) * M == M * (P + Q)"),
                Direction.BACKWARD,
            ),
            {ex("P * M + Q * M == M * (P + Q)")},
        )

    def test_distribute_left(self):
        self.assertEqual(
            try_rule(
                forall((A, B, R), ex("R * (A + B) == R * A + R * B")),
                ex("P * M + Q * M == M * (P + Q)"),
                Direction.BACKWARD,
            ),
            {ex("P * M + Q * M == M * P + M * Q")},
        )

    def test_known_property_of_P(self):
        self.assertEqual(
            try_rule(
                ex("P * M == M * P"),
                ex("P * M + Q * M == M * P + M * Q"),
                Direction.BACKWARD,
            ),
            {
                ex("M * P + Q * M == M * P + M * Q"),
                ex("P * M + Q * M == P * M + M * Q"),
            },
        )

    def test_known_property_of_Q(self):
        self.assertEqual(
            try_rule(
                ex("Q * M == M * Q"),
                ex("P * M + Q * M == M * P + M * Q"),
                Direction.BACKWARD,
            ),
            {
                ex("P * M + M * Q == M * P + M * Q"),
                ex("P * M + Q * M == M * P + Q * M"),
            },
        )

    def test_cancel_both_sides(self):
        self.assertEqual(
            try_rule(
                forall((P, Q, R), ex("P + Q == P + R <==> Q == R")),
                ex("M * P + Q * M == M * P + M * Q"),
                Direction.BACKWARD,
            ),
            {
                ex("Q * M == M * Q"),
                ex("P + (M * P + Q * M) == P + (M * P + M * Q)"),
            },
        )

    def test_no_match(self):
        self.assertEqual(
            try_rule(
                forall(P, ex("P + Q == Q + P")),
                ex("A and B"),
                Direction.BACKWARD,
            ),  # backwards
            set(),
        )

    def test_match_under_match(self):
        self.assertEqual(
            try_rule(
                forall((A, B), ex("A + B == B + A")),
                ex("X + Y + Z"),
                Direction.BACKWARD,
            ),  # backwards
            {ex("Z + (X + Y)"), ex("Y + X + Z")},
        )

    def test_not_recursive(self):
        self.assertEqual(
            try_rule(
                forall((P, Q), ex("P and Q ==> P")),
                ex("not ( P and Q)"),
                Direction.FORWARD,
            ),  # backwards
            set(),
        )

    def test_only_match_boolean(self):
        self.assertEqual(
            try_rule(
                forall((P,), ex("P and P <==> P")),
                ex("A and B"),
                Direction.BACKWARD,
            ),  # backwards
            {
                ex("(A and A) and B"),
                ex("(A and B) and (A and B)"),
                ex("A and (B and B)"),
            },
        )

    def test_matrix_mult(self):
        self.assertEqual(
            try_rule(
                forall(
                    (a, b, c, d, p, q, r, s),
                    ex(
                        "[a b; c d] * [p q; r s] =="
                        "   [a * p + b * r   a * q + b * s;"
                        "    c * p + d * r   c * q + d * s]"
                    ),
                ),
                ex("[1 1; 1 1] * [1 1; 0 1]"),
                Direction.FORWARD,
            ),  # Direction is ignored for == I think.
            {
                ex(
                    "[1 * 1 + 1 * 0   1 * 1 + 1 * 1;"
                    " 1 * 1 + 1 * 0   1 * 1 + 1 * 1]"
                )
            },
        )

    def test_bound_vs_free_vars(self):
        # with self.assertRaises(AssertionError):
        self.assertEqual(
            try_rule(
                ex("a == b"), forall(a, ex("a + a == 2 * a")), Direction.FORWARD
            ),
            set(),
        )


if __name__ == "__main__":
    with typeguard.TypeChecker(["MatchAndSubstitute", "Expression", "Parser"]):
        unittest.main()
