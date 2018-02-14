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

import Parser
from Deduction import *
import tokenize
# from pprint import pprint

P = var('P')
Q = var('Q')
R = var('R')
A = var('A')
B = var('B')
M = var('M')

a = var('a')
b = var('b')
c = var('c')
d = var('d')

p = var('p')
q = var('q')
r = var('r')
s = var('s')


def ex(string):
    return Parser.parse(string)


class TestParser(unittest.TestCase):
    def test_malformed(self):
        with self.assertRaises(SyntaxError):
            ex('+')

    def test_malformed2(self):
        with self.assertRaises(SyntaxError):
            ex('P Q')

    def test_malformed3(self):
        with self.assertRaises(tokenize.TokenError):
            ex('( P')

    def test_mult(self):
        self.assertEqual(ex('P*Q'), P * Q)

    def test_mult2(self):
        self.assertEqual(ex('P*Q*R'), (P * Q) * R)

    def test_mult3(self):
        self.assertEqual(ex('P*(Q*R)'), P * (Q * R))

    def test_mult4(self):
        self.assertEqual(ex('(P*Q)*R'), (P * Q) * R)

    def test_add_mult(self):
        self.assertEqual(ex('P + Q*R'), P + Q * R)

    def test_add_mult2(self):
        self.assertEqual(ex('P * Q+R'), P * Q + R)

    def test_add_mult3(self):
        self.assertEqual(ex('(P + Q) * R'), (P + Q) * R)

    def test_add_mult4(self):
        self.assertEqual(ex('P * (Q + R)'), P * (Q + R))

    def test_compare(self):
        self.assertEqual(
            ex('R * (P + Q) == R * P + R * Q'),
            equal(R * (P + Q), R * P + R * Q))

    def test_in(self):
        self.assertEqual(
            ex('P + Q in B'),
            in_(P + Q, B))

    def test_not(self):
        self.assertEqual(
            ex('not P == Q'),
            not_(equal(P, Q)))

    def test_not2(self):
        self.assertEqual(
            ex('not P and Q'),
            and_(not_(P), Q))

    def test_not3(self):
        self.assertEqual(
            ex('P or not Q'),
            or_(P, not_(Q)))

    def test_implies(self):
        self.assertEqual(
            ex('not P or Q ==> A and B'),
            implies(or_(not_(P), Q), and_(A, B)))

    def test_iff(self):
        self.assertEqual(
            ex('not P or Q <==> (P ==> Q)'),
            iff(or_(not_(P), Q), implies(P, Q)))

    def test_implies_precedence(self):
        self.assertEqual(
            ex('P ==> Q and not Q ==> not P'),
            implies(implies(P, and_(Q, not_(Q))), not_(P)))

    def test_implies_precedence2(self):
        self.assertEqual(
            ex('(P ==> Q) and not Q ==> not P'),
            implies(and_(implies(P, Q), not_(Q)), not_(P)))

    def test_implies_precedence3(self):
        self.assertEqual(
            ex('((P ==> Q) and not Q) ==> not P'),
            implies(and_(implies(P, Q), not_(Q)), not_(P)))

    # # Python syntax for lists.
    # def test_list(self):
    #     self.assertEqual(
    #         ex('[P, P ==> Q, P * R]'),
    #         list_(P, implies(P, Q), multiply(P, R)))

    def test_matrix(self):
        self.assertEqual(
            ex('[P Q; Q R]'),
            matrix_literal(list_literal(P, Q), list_literal(Q, R)))

        self.assertEqual(
            ex('M == [1 1; 0 1]'),
            equal(M,
                  matrix_literal(list_literal(num(1), num(1)),
                                 list_literal(num(0), num(1)))))

    def test_number_literal(self):
        self.assertEqual(ex('0'), num(0))
        self.assertEqual(ex('1'), num(1))
        self.assertEqual(ex('954'), num(954))

        # Apparently, Python parses "054" as two NUMBERs, 0 and 54.  Strange.
        # self.assertEqual(ex('054'), num(54))

        # -5 would be parsed as a unary minus applied to num(5), but we don't
        # have unary minus yet.
        # self.assertEqual(ex('-5'), minus(num(5)))


class TestRepr(unittest.TestCase):
    def cannonical(self, expr: str) -> None:
        assert isinstance(expr, str)
        self.assertEqual(repr(ex(expr)), expr)

    def test_mult_add(self):
        self.cannonical('P * Q + R')

        self.cannonical('P * (Q + R)')

    def test_not(self):
        self.cannonical('not P')

    def test_not2(self):
        self.cannonical('not (P and Q)')

    def test_forall(self):
        self.assertEqual(repr(
            forall(P, ex('P ==> P'))),
            r'\forall(P, P ==> P)')

        self.assertEqual(repr(
            forall((P, Q), ex('P + Q == Q + P'))),
            r'\forall((P, Q), P + Q == Q + P)')

    def test_exists(self):
        self.assertEqual(repr(
            exists(A, ex('A + A == A'))),
            r'\exists(A, A + A == A)')

    def test_in(self):
        self.assertEqual(repr(
            in_(P, B)),
            r'P \in B')

    def test_number_literal(self):
        self.assertEqual(repr(
            num(15)),
            '15')

    def test_list_literal(self):
        self.assertEqual(repr(
            list_literal(num(5), a, b)),
            '[5, a, b]')

    def test_matrix_literal(self):
        self.assertEqual(repr(
                           matrix_literal(list_literal(num(5), a, b),
                                          list_literal(num(0), c, d))),
                         '[5  a  b; 0  c  d]')

    def test_matrix_literal_nonstandard(self):
        self.assertEqual(repr(
                           matrix_literal(list_literal(num(5), a, b),
                                          sum_(num(3), list_literal(num(0), c,
                                                                 d)))),
                         '[[5, a, b], 3 + [0, c, d]]')


class TestMatch(unittest.TestCase):
    def test_node(self):
        self.assertEqual(
            match({P}, P, P + Q),
            {P: (P + Q)})

    def test_sum(self):
        self.assertEqual(
            match({P}, P + B, Q + B),
            {P: Q})

    def test_different_root(self):
        self.assertIsNone(
            match(set(), P + Q, P * Q))

    def test_different_len(self):
        self.assertIsNone(
            match(set(), P + Q, sum_(P, Q, A)))

    def test_simple(self):
        self.assertEqual(
            match({P}, ex('P in B'), ex('P + Q in B')),
            {P: (P + Q)})

    def test_dummy_appears_twice(self):
        self.assertEqual(
            match({P}, ex('P in P'), ex('P + Q in P + Q')),
            {P: (P + Q)})

    def test_dummy_appears_twice2(self):
        self.assertIsNone(
            match({P}, ex('P in P'), ex('P + Q in P + B')))

    def test_two_dimmies(self):
        self.assertEqual(
            match({P, Q}, P + Q, A + B),
            {P: A, Q: B})

    def test_number_literal(self):
        self.assertEqual(
            match({a}, a, num(1)),
            {a: num(1)})

    def test_matrix_literal(self):
        self.assertEqual(
            match({a, b, c, d}, ex('[a b; c d]'), ex('[1 2; 3 4]')),
            {a: num(1), b: num(2), c: num(3), d: num(4)})


class TestIsInstance(unittest.TestCase):
    def test_reflexivity_of_equals(self):
        self.assertEqual(
            is_instance(ex('M * P + M * Q == M * P + M * Q'),
                        forall(A, ex('A == A')),
                        set()),
            {A: ex('M * P + M * Q')})

    def test_distributed_law(self):
        self.assertEqual(
            is_instance(ex('(P + Q) * M == P * M + Q * M'),
                        forall((A, B, M), ex('(A + B) * M == A * M + B * M'))),
            {A: P, B: Q, M: M})


class TestIsRule(unittest.TestCase):
    def test_equals(self):
        self.assertTrue(is_rule(ex('P * M == M * P')))

    def test_equivalent(self):
        self.assertTrue(is_rule(ex('A and B <==> B and A')))

    def test_implies(self):
        self.assertTrue(is_rule(ex('(P and P ==> Q) ==> Q')))

    def test_forall_equals(self):
        self.assertTrue(is_rule(forall((P, M), ex('P * M == M * P'))))


class TestTryRule(unittest.TestCase):
    def test_doesnt_match(self):
        self.assertEqual(
            try_rule(forall((P, Q, R), ex('(P + Q) * R == P * R + Q * R')),
                     ex('P + Q in B'),
                     Direction.BACKWARD),
            set())

    def test_modus_tollens(self):
        self.assertEqual(
            try_rule(forall((P, Q), ex('((P ==> Q) and not Q) ==> not P')),
                     ex('not B'),
                     Direction.BACKWARD),
            {ex('(B ==> Q) and not Q')})

    def test_modus_ponens(self):
        self.assertEqual(
            try_rule(forall((P, Q), ex('((P ==> Q) and P) ==> Q')),
                     ex('(A ==> B) and A'),
                     Direction.FORWARD),
            {ex('B')})

    def test_definition_of_set(self):
        self.assertEqual(
            try_rule(forall(P, ex("P in B <==> P * M == M * P")),
                     ex("P + Q in B"),
                     Direction.BACKWARD),
            {ex('(P + Q) * M == M * (P + Q)')})

    def test_distribute_right(self):
        self.assertEqual(
            try_rule(forall((A, B, R), ex('(A + B) * R == A * R + B * R')),
                     ex('(P + Q) * M == M * (P + Q)'),
                     Direction.BACKWARD),
            {ex('P * M + Q * M == M * (P + Q)')})

    def test_distribute_left(self):
        self.assertEqual(
            try_rule(forall((A, B, R), ex('R * (A + B) == R * A + R * B')),
                     ex('P * M + Q * M == M * (P + Q)'),
                     Direction.BACKWARD),
            {ex('P * M + Q * M == M * P + M * Q')})

    def test_known_property_of_P(self):
        self.assertEqual(
            try_rule(ex('P * M == M * P'),
                     ex('P * M + Q * M == M * P + M * Q'),
                     Direction.BACKWARD),
            {ex('M * P + Q * M == M * P + M * Q'),
             ex('P * M + Q * M == P * M + M * Q')})

    def test_known_property_of_Q(self):
        self.assertEqual(
            try_rule(ex('Q * M == M * Q'),
                     ex('P * M + Q * M == M * P + M * Q'),
                     Direction.BACKWARD),
            {ex('P * M + M * Q == M * P + M * Q'),
             ex('P * M + Q * M == M * P + Q * M')})

    def test_cancel_both_sides(self):
        self.assertEqual(
            try_rule(forall((P, Q, R), ex('P + Q == P + R <==> Q == R')),
                     ex('M * P + Q * M == M * P + M * Q'),
                     Direction.BACKWARD),
            {ex('Q * M == M * Q'),
             ex('P + (M * P + Q * M) == P + (M * P + M * Q)')})

    def test_no_match(self):
        self.assertEqual(
            try_rule(forall(P, ex('P + Q == Q + P')),
                     ex('A and B'),
                     Direction.BACKWARD),  # backwards
            set())

    def test_match_under_match(self):
        self.assertEqual(
            try_rule(forall((A, B), ex('A + B == B + A')),
                     ex('X + Y + Z'),
                     Direction.BACKWARD),  # backwards
            {ex('Z + (X + Y)'), ex('Y + X + Z')})

    def test_not_recursive(self):
        self.assertEqual(
            try_rule(forall((P, Q), ex('P and Q ==> P')),
                     ex('not ( P and Q)'),
                     Direction.FORWARD),  # backwards
            set())

    def test_only_match_boolean(self):
        self.assertEqual(
            try_rule(forall((P,), ex('P and P <==> P')),
                     ex('A and B'),
                     Direction.BACKWARD),  # backwards
            {ex('(A and A) and B'),
             ex('(A and B) and (A and B)'),
             ex('A and (B and B)')})

    def test_matrix_mult(self):
        self.assertEqual(
            try_rule(forall((a, b, c, d, p, q, r, s),
                            ex('[a b; c d] * [p q; r s] =='
                                '   [a * p + b * r   a * q + b * s;'
                                '    c * p + d * r   c * q + d * s]')),
                     ex('[1 1; 1 1] * [1 1; 0 1]'),
                     Direction.FORWARD),  # Direction is ignored for == I think.
            {ex('[1 * 1 + 1 * 0   1 * 1 + 1 * 1;'
                ' 1 * 1 + 1 * 0   1 * 1 + 1 * 1]')})


class TestPathLength(unittest.TestCase):
    # Modifies inputs (sorts them).
    def assert_path_length_result(self, actual, expected):
        # Make sure its in order by the first argument.
        for i in range(len(actual) - 1):
            self.assertLessEqual(actual[i][0], actual[i + 1][0])

        self.assertEqual(actual.sort(key=lambda x: (x[0], id(x))),
                         expected.sort(key=lambda x: (x[0], id(x))))

    def test_simple(self):
        self.assert_path_length_result(
            path_length(P, M, ex('(P + Q) * M == M * (P + Q)')),
            [(3, P, M), (3, P, M), (5, P, M), (5, P, M)])

        #         ===
        #     *         *
        #   +   M     M   +
        # P   Q         P   Q

    def test_simple2(self):
        self.assert_path_length_result(
            path_length(M, P, ex('(P + Q) * M == M * (P + Q)')),
            [(3, M, P), (3, M, P), (5, M, P), (5, M, P)])


if __name__ == '__main__':  # pragma: no cover
    unittest.main()
