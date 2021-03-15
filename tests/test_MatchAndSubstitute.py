import unittest

from MatchAndSubstitute import match, is_instance, is_rule, try_rule, \
    Direction, rename_quantified
import Parser
from Expression import var, sum_, num, forall, ExpressionType
# import typeguard

OBJECT = ExpressionType.OBJECT
PROPOSITION = ExpressionType.PROPOSITION

A = var("A", OBJECT)
_A = var("_A", OBJECT)
B = var("B", OBJECT)
C = var("C", OBJECT)
M = var("M", OBJECT)

P = var("P", PROPOSITION)
Q = var("Q", PROPOSITION)

U = var("U", PROPOSITION)
V = var("V", PROPOSITION)

R = var("R", OBJECT)

a = var("a", OBJECT)
_a = var("_a", OBJECT)
b = var("b", OBJECT)
c = var("c", OBJECT)
d = var("d", OBJECT)

p = var("p", OBJECT)
q = var("q", OBJECT)
r = var("r", OBJECT)
s = var("s", OBJECT)

x = var("x", OBJECT)
y = var("y", OBJECT)
z = var("z", OBJECT)


def ex(string):
    return Parser.parse(string)


ANY = ExpressionType.ANY


class TestMatch(unittest.TestCase):

    def test_node(self):
        self.assertEqual({A: (A + B)},
                         match({'A': A}, A, A + B))

    def test_sum(self):
        self.assertEqual({A: C},
                         match({'A': A}, A + B, C + B))

    def test_different_root(self):
        self.assertIsNone(match({}, A + B, A * B))

    def test_different_len(self):
        # I'm not sure sum_(A, B, C) should be allowed; addition is only
        # defined on two arguments, not 3.  Oh well.
        self.assertIsNone(match({}, A + B, sum_(A, B, C)))

    def test_simple(self):
        self.assertEqual({A: (A + C)},
                         match({'A': A}, ex("A in B"), ex("A + C in B")),
        )

    def test_dummy_appears_twice(self):
        self.assertEqual(
            match({'A': A}, ex("A in A"), ex("A + B in A + B")), {A: (A + B)}
        )

    def test_dummy_appears_twice2(self):
        self.assertIsNone(match({'A': A}, ex("A in A"), ex("A + B in A + "
                                                               "C")))

    def test_two_dummies(self):
        self.assertEqual({x: A, y: B},
                        match({'x': x, 'y': y}, x + y, A + B))

    def test_number_literal(self):
        self.assertEqual(match({'a': a}, a, num(1)), {a: num(1)})

    def test_matrix_literal(self):
        self.assertEqual(
            match({'a': a, 'b': b, 'c': c, 'd': d},
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
                ex("(A + B) * M == A * M + B * M"),
                forall((x, y, M), ex("(x + y) * M == x * M + y * M")),
            ),
            {x: A, y: B, M: M},
        )


class TestRenameQuantified(unittest.TestCase):

    def test_eq_bound_variable(self):
        """Test that equality takes the name of the bound variable into
        account.

        The variables that we quantify over are a special case in the code.
        When first changed to a special case, I didn't implement __eq__ on
        Quantifier.  So, TestRenameQuant.test_simple didn't test that
        Quantifier._variables_map.keys() were renamed, only that the child
        expression was renamed.
        """
        self.assertNotEqual(forall(_a, ex('a + 0 == a')),
                            forall(a, ex('a + 0 == a')))

        self.assertEqual(forall(a, ex('a + 0 == a')),
                         forall(a, ex('a + 0 == a')))

    def test_simple(self):
        self.assertEqual(
            forall(_a, ex('_a + 0 == _a')),
            rename_quantified(forall(a, ex('a + 0 == a')), {'a', 'b'}))

    def test_overlapping(self):
        self.assertEqual(
            forall((var('__a', OBJECT), _a), ex('_a * __a == 0')),
            rename_quantified(forall((a, _a), ex('_a * a == 0')),
                              {'a', 'M'}))

    def test_hmm(self):
        renamed = rename_quantified(forall((a, _a), ex('_a * a == 0')),
                          {'a', '_a'})
        # Order of renaming can be different in different runs, thanks to
        # set() being non deterministic.  That's ok.
        vars = (var('__a', OBJECT), var('___a', OBJECT))

        self.assertIn(
            renamed,
            {forall(vars, ex("__a * ___a == 0")),
             forall(vars, ex("___a * __a == 0"))})


class TestIsRule(unittest.TestCase):

    def test_equals(self):
        self.assertTrue(is_rule(ex("P * M == M * P")))

    def test_equivalent(self):
        self.assertTrue(is_rule(ex("A and B <==> B and A")))

    def test_implies(self):
        self.assertTrue(is_rule(ex("(P and P ==> Q) ==> Q")))

    def test_forall_equals(self):
        self.assertTrue(is_rule(forall((A, M), ex("A * M == M * A"))))


class TestTryRule(unittest.TestCase):

    def test_doesnt_match(self):
        self.assertEqual(
            try_rule(
                forall((A, B, C), ex("(A + B) * C == A * C + B * C")),
                ex("A + B in R"),
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
                ex("(U ==> V) and U"),
                Direction.FORWARD,
            ),
            {V},
        )

    def test_definition_of_set(self):
        self.assertEqual(
            try_rule(
                forall(A, ex("A in B <==> A * M == M * A")),
                ex("A + C in B"),
                Direction.BACKWARD,
            ),
            {ex("(A + C) * M == M * (A + C)")},
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
                forall((A, B, C), ex("A + B == A + C <==> B == C")),
                ex("M * A + B * M == M * A + M * B"),
                Direction.BACKWARD,
            ),
            {
                ex("B * M == M * B"),
                forall(_A, ex("_A + (M * A + B * M) == _A + (M * A + M * B)")),
            },
        )

    def test_no_match(self):
        self.assertEqual(
            try_rule(
                forall(A, ex("A + B == B + A")),
                ex("P and Q"),
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
                forall((B, C), ex("1 * B == C")),
                Direction.FORWARD
            ),
            {forall((B, C), ex('B == C'))},
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
