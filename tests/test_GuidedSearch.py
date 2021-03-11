import unittest
from GuidedSearch import Guidance
from Expression import *
from MatchAndSubstitute import try_rule, Direction, match_and_substitute
import Parser


def ex(st: str) -> Expression:
    return Parser.parse(st)


a = var("a")
b = var("b")
c = var("c")

additive_inverse_right: CompositeExpression = \
    forall(a, exists(b, ex("a + b == 0")))


field_axioms: list[CompositeExpression] = [
    # associative
    forall((a, b, c), ex("(a + b) + c == a + (b + c)")),
    forall((a, b, c), ex("(a * b) * c == a * (b * c)")),

    # commutative
    forall((a, b, c), ex("a + b == b + a")),
    forall((a, b, c), ex("a * b == b * a")),

    # identity
    forall(a, ex("a + 0 == a")),
    forall(a, ex("0 + a == a")),
    forall(a, ex("a * 1 == a")),
    forall(a, ex("1 * a == a")),

    # inverse
    additive_inverse_right,
    forall(a, exists(b, ex("b + a == 0"))),
    forall(a, implies(ex("a != 0"), exists(b, ex("a * b == 1")))),
    forall(a, implies(ex("a != 0"), exists(b, ex("b * a == 1")))),

    # distributive
    forall((a, b, c), ex("a * (b + c) == a * b + a * c")),

    # Do I need to add 1 != 0?
]


class TestGuidance(unittest.TestCase):
    def setUp(self) -> None:
        self.guidance = Guidance()

    def test_x(self) -> None:
        self.assertTrue(self.guidance.ok(var('x'), True))
        self.assertFalse(self.guidance.ok(var('x'), False))

    def test_num_literal(self) -> None:
        self.assertFalse(self.guidance.ok(num(23), True))
        self.assertTrue(self.guidance.ok(num(23), False))

    def test_add(self) -> None:
        self.assertFalse(self.guidance.ok(Sum(), True))
        self.assertFalse(self.guidance.ok(Sum(), False))


def try_match(rule: CompositeExpression, target: Expression,
              direction: Direction,
              dummies: Optional[FrozenSet[Variable]] = None,
              definitions: Optional[FrozenSet[Variable]] = None) -> Set[
    Expression]:
    if dummies is None:
        dummies = frozenset()

    if has_head(rule, ForAll):
        return try_match(
            rule[1],
            target,
            direction,
            dummies.union(rule.get_variables(dummies)),
            definitions,
        )

    if definitions is None:
        definitions = frozenset()

    if has_head(rule, Exists):
        # I guess we need another argument to this function, for definitions?
        # The idea is that we gensym a witness, add definition to list of
        # definitions, then can recurse.]
        return try_match(rule[1],
                         target,
                         direction,
                         dummies,
                         definitions.union(rule.get_variables(
                             definitions.union(dummies))))

    # For now, only implement for ==.
    assert has_head(rule, Equal)

    assert dummies.isdisjoint(target.bound_variables())
    assert dummies.isdisjoint(target.free_variables(frozenset()))

    assert definitions.isdisjoint(target.bound_variables())
    assert definitions.isdisjoint(target.free_variables(frozenset()))

    # Recursing on the rule, rather than the target, seems ... kind of
    # desperate.  It's only in special cases that you can hope that you'll be
    # able to make progress that way.
    #
    # So there are two ways to proceed.  Think of it purely formally, e.g.
    # (= (+ x 7) 11) and how to manipulate that tree.  Or think of it more
    # like a middle schooler: on the left you have x + 7 beads, on the right
    # you have 11 beads, and you can add or subtract beads from both sides to
    # try to get x alone.
    #
    # From
    # https://bestedlessons.org/2019/04/04/9-excellent-middle-school-math-textbooks-with-solutions/
    # in grade 7 they solve simple equations like x + 7 = 11 or 5y = 20 with
    # "mental math," which seems to boil down to "it's obvious," with the
    # reminder that division is the opposite of multiplication.

    res = match_and_substitute(dummies, rule[1], rule[2], target)

    assert False

    return res

class TestDecideOnAdditiveInverse(unittest.TestCase):
    def setUp(self) -> None:
        self.guidance = Guidance()

    def test_stuff(self) -> None:
        # We'll just focus on LHS for now.
        #
        # Simulate already having seen and solved x + 0 and x + 0 + 0
        self.guidance.lhs.update({0, Sum})

        premise = Parser.parse('x + 7')

        self.assertEqual(self.guidance.not_matching(premise), num(7))

        # So now we need to find the premises that we can match with "7".
        print(try_match(additive_inverse_right, num(7), Direction.FORWARD))

        self.assertTrue(False)

        # for axiom in field_axioms:
            # match isn't what we want.  It only matches at root, and doesn't
            # know about implies, forall, etc.
            #
            # Maybe want try_rule(), at least for now?
            # try_rule(axiom, num(7), Direction.FORWARD)


if __name__ == '__main__':
    unittest.main()
