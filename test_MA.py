import unittest

# To run tests:
#
# coverage run --branch test_MA.py && coverage report --show-missing

# To enter the debugger when a test fails, uncomment this line:
# unittest.TestCase.run = lambda self, *args, **kw: unittest.TestCase.debug(self)
# python3 -m pdb -c continue test_MA.py

from Expression import *
import Parser
from Deduction import *

P = var('P')
Q = var('Q')
R = var('R')
A = var('A')
B = var('B')


def ex(input):
    return Parser.parse(input)


class TestParser(unittest.TestCase):
    def test_malformed(self):
        with self.assertRaises(SyntaxError):
            ex('+')

    def test_malformed2(self):
        with self.assertRaises(SyntaxError):
            ex('P Q')

    def test_mult(self):
        self.assertEqual(ex('P*Q'), P * Q)

    def test_mult2(self):
        self.assertEqual(ex('P*Q*R'), (P * Q) * R)

    def test_mult3(self):
        self.assertEqual(ex('P*(Q*R)'), P * (Q * R))

    def test_mult3(self):
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
            match(set(), P + Q, sum(P, Q, A)))

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


class TestTryRule(unittest.TestCase):
    def test_doesnt_match(self):
        self.assertEqual(
            try_rule(set(),
                     forall([P, Q, R], ex('(P + Q) * R == P * R + Q * R')),
                     ex('P + Q in B')),
            set())

    def test_modus_tollens(self):
        self.assertEqual(
            try_rule(set(),
                     forall([P, Q, R], ex('((P ==> Q) and not Q) ==> not P')),
                     ex('not B')),
            {ex('(B ==> Q) and not Q')})

    def test_definition_of_set(self):
        self.assertEqual(
            try_rule(set(),
                     forall(P, ex("P in B <==> P * M == M * P")),
                     ex("P + Q in B")),
            {ex('(P + Q) * M == M * (P + Q)')})

    def test_distribute_right(self):
        self.assertEqual(
            try_rule(set(),
                     forall([P, Q, R], ex('(P + Q) * R == P * R + Q * R')),
                     ex('(P + Q) * M == M * (P + Q)')),
            {ex('P * M + Q * M == M * (P + Q)')})

    def test_distribute_left(self):
        self.assertEqual(
            try_rule(set(),
                     forall([P, Q, R], ex('R * (P + Q) == R * P + R * Q')),
                     ex('P * M + Q * M == M * (P + Q)')),
            {ex('P * M + Q * M == M * P + M * Q')})

    def test_known_property_of_P(self):
        self.assertEqual(
            try_rule(set(),
                     ex('P * M == M * P'),
                     ex('P * M + Q * M == M * P + M * Q')),
            {ex('M * P + Q * M == M * P + M * Q'),
             ex('P * M + Q * M == P * M + M * Q')})

    def test_known_property_of_Q(self):
        self.assertEqual(
            try_rule(set(),
                     ex('Q * M == M * Q'),
                     ex('P * M + Q * M == M * P + M * Q')),
            {ex('P * M + M * Q == M * P + M * Q'),
             ex('P * M + Q * M == M * P + Q * M')})

    def test_cancel_both_sides(self):
        self.assertEqual(
            try_rule(set(),
                     forall([P, Q, R], ex('P + Q == P + R <==> Q == R')),
                     ex('M * P + Q * M == M * P + M * Q')),
            {ex('Q * M == M * Q'),
             ex('P + (M * P + Q * M) == P + (M * P + M * Q)')})


if __name__ == '__main__':
    unittest.main()
