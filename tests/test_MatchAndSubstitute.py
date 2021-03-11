import unittest

from MatchAndSubstitute import match, is_instance, is_rule, try_rule, \
    Direction, rename_quantified
import Parser
from Expression import var, sum_, num, forall, ExpressionType
# import typeguard

A = var("A")
B = var("B")
M = var("M")

P = var("P")
_P = var("_P")
Q = var("Q")
R = var("R")

a = var("a")
_a = var("_a")
b = var("b")
c = var("c")
d = var("d")

p = var("p")
q = var("q")
r = var("r")
s = var("s")


def ex(string):
    return Parser.parse(string)


ANY = ExpressionType.ANY


class TestMatch(unittest.TestCase):

    def test_node(self):
        self.assertEqual(match({P: ANY}, P, P + Q), {P: (P + Q)})

    def test_sum(self):
        self.assertEqual(match({P: ANY}, P + B, Q + B), {P: Q})

    def test_different_root(self):
        self.assertIsNone(match({}, P + Q, P * Q))

    def test_different_len(self):
        self.assertIsNone(match({}, P + Q, sum_(P, Q, A)))

    def test_simple(self):
        self.assertEqual(
            match({P: ANY}, ex("P in B"), ex("P + Q in B")), {P: (P + Q)}
        )

    def test_dummy_appears_twice(self):
        self.assertEqual(
            match({P: ANY}, ex("P in P"), ex("P + Q in P + Q")), {P: (P + Q)}
        )

    def test_dummy_appears_twice2(self):
        self.assertIsNone(match({P: ANY}, ex("P in P"), ex("P + Q in P + B")))

    def test_two_dummies(self):
        self.assertEqual(match({P: ANY, Q: ANY}, P + Q, A + B), {P: A, Q: B})

    def test_number_literal(self):
        self.assertEqual(match({a: ANY}, a, num(1)), {a: num(1)})

    def test_matrix_literal(self):
        self.assertEqual(
            match({a: ANY, b: ANY, c: ANY, d: ANY},
                  ex("[a b; c d]"), ex("[1 2; 3 4]")),
            {a: num(1), b: num(2), c: num(3), d: num(4)},
        )


class TestIsInstance(unittest.TestCase):

    def test_reflexivity_of_equals(self):
        self.assertEqual(
            is_instance(
                ex("M * P + M * Q == M * P + M * Q"),
                forall(A, ex("A == A")),
                {},
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


class TestRenameQuantified(unittest.TestCase):

    def test_eq_bound_variable(self):
        """Test that equality takes the name of the bound variable into
        account.

        The variables that we quantify over are a special case in the code.
        When first changed to a special case, I didn't implement __eq__ on
        Quantifier.  So, TestRenameQuant.test_simple didn't test that
        Quantifier._variables were renamed, only that the child expression
        was renamed.
        """
        self.assertNotEqual(forall(_a, ex('a + 0 == a')),
                            forall(a, ex('a + 0 == a')))

        self.assertEqual(forall(a, ex('a + 0 == a')),
                         forall(a, ex('a + 0 == a')))

    def test_simple(self):
        self.assertEqual(
            forall(_a, ex('_a + 0 == _a')),
            rename_quantified(forall(a, ex('a + 0 == a')), {a, b}))

    def test_overlapping(self):
        self.assertEqual(
            forall((var('__a'), _a), ex('_a * __a == 0')),
            rename_quantified(forall((a, _a), ex('_a * a == 0')),
                              {a, M}))

    def test_hmm(self):
        self.assertEqual(
            forall((var('__a'), var('___a')), ex("___a * __a == 0")),
            rename_quantified(forall((a, _a), ex('_a * a == 0')),
                              {a, _a}))


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
                forall(_P, ex("_P + (M * P + Q * M) == _P + (M * P + M * Q)")),
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
        # What, exactly, is this test supposed to be testing?
        self.assertEqual(
            try_rule(
                forall((P, Q), ex("P and Q <==> Q and P")),
                ex("A and B"),
                Direction.BACKWARD,
            ),
            {
                ex("B and A"),
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

    def test_free_variables_on_tuple(self):
        # What's the bug this is trying to test for?  I should really
        # document that from now on.
        self.assertEqual(
            try_rule(
                forall(a, ex("1 * a == a")),
                forall((P, Q), ex("1 * P == Q")),
                Direction.FORWARD
            ),
            {forall((P, Q), ex('P == Q'))},
        )

    def test_rename(self):
        """Test quantifier applied to quantifier, with the same var name.

        """
        self.assertEqual(
            try_rule(
                forall(a, ex('0 * a == 0')),
                forall(a, ex('0 * a == 0')),
                Direction.FORWARD
            ),
            {
                forall((a, _a), ex('(0 * _a) * a == 0')),
                forall((a, _a), ex('0 * a == 0 * _a')),
                ex('0 == 0'),
            },
        )

    def test_name_collision(self):
        self.assertEqual(
            try_rule(
                forall((a, _a), ex("_a * a == 0")),
                forall(a, ex("M == a")),
                Direction.FORWARD),
            frozenset()
        )


if __name__ == "__main__":
    # with typeguard.TypeChecker(["MatchAndSubstitute", "Expression",
    # "Parser"]):
    unittest.main()
