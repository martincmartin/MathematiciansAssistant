import unittest
from GuidedSearch import Guidance, GuidedSimplify
from Expression import *
from MatchAndSubstitute import try_rule, Direction, match_and_substitute
import Parser

OBJECT = ExpressionType.OBJECT


def ex(st: str) -> Expression:
    return Parser.parse(st)


a = var("a", OBJECT)
b = var("b", OBJECT)
c = var("c", OBJECT)

x = var("x", OBJECT)

# Following Lean's lead, we don't use the usual "exists additive inverse" axiom,
# because there's no constructive way to turn it into a function.  In group
# theory, Lean takes the unary minus function as an axiom.  Here we take the 2
# arg ones as axiom, since that's more natural to most middle schoolers.
subtraction = forall([a, b, c], ex("a - b == c <==> a == b + c"))

# additive_inverse_right: CompositeExpression = forall(a, exists(b, ex("a + b == 0")))

additive_identity = forall(a, ex("a + 0 == a"))


field_axioms: list[CompositeExpression] = [
    # associative
    forall((a, b, c), ex("(a + b) + c == a + (b + c)")),
    forall((a, b, c), ex("(a * b) * c == a * (b * c)")),
    # commutative
    forall((a, b, c), ex("a + b == b + a")),
    forall((a, b, c), ex("a * b == b * a")),
    # identity
    additive_identity,
    forall(a, ex("0 + a == a")),
    forall(a, ex("a * 1 == a")),
    forall(a, ex("1 * a == a")),
    # inverse
    subtraction,
    forall([a, b, c], ex("b != 0 ==> (a / b == c <==> a == b * c)")),
    # distributive
    forall((a, b, c), ex("a * (b + c) == a * b + a * c")),
    # Do I need to add 1 != 0?
]


class TestGuidedSimplify(unittest.TestCase):
    def test_x_plus_0(self):
        gs = GuidedSimplify(field_axioms, ex("x + 0"))

        # Start by iterating over all rules, and trying to apply them at
        # every spot in an expression.

        success = gs.brute_force(x)
        if success:
            print("SUCCESS!!")

        # Attempt number two.  Really should separate out proof state from
        # learning.  Oh well.
        gs.solveme(ex("(x + 0) + 0"), x)

        gs.solveme(ex("0 + x"), x)

        print("********** Attempting 7 - 7")
        gs.solveme(ex("7 - 7"), num(0))

        # So we get to:
        # a - b == c <==> a == b + c dummies a, b, c.  But no further.
        # So we need to recognize <==> (and =>) and try the relevant side(s).

        # Next up: simplify 7 - 7.
        #
        # We take the subtraction function (i.e. 2-arg minus) as given, and the
        # following property:
        #
        # forall(x, y, z){x - y = z <=> x = z + y}
        #
        # Substitute in 7 & 7:
        #
        # forall(z){7 - 7 = z <=> 7 = z + 7}
        #
        # By additive identity, 0 + 7 = 7, therefore 7 - 7 = 0.
        #
        # So how do we think of substituting 7 & 7?  Well, the only thing we
        # know about subtraction is that axiom, so we need to find things of the
        # form "x = z + y".  And looking over our axioms, additive identity fits
        # the bill nicely: a = 0 + a.  So we can easily prove forall a, a - a = 0.

        print("**********  Can now solve")
        for start, rule in gs.algorithms.items():
            print(f"{start}    using {rule}")


# class TestGuidance(unittest.TestCase):
#     def setUp(self) -> None:
#         self.guidance = Guidance()
#
#     def test_x(self) -> None:
#         self.assertTrue(self.guidance.ok(var('x'), True))
#         self.assertFalse(self.guidance.ok(var('x'), False))
#
#     def test_num_literal(self) -> None:
#         self.assertFalse(self.guidance.ok(num(23), True))
#         self.assertTrue(self.guidance.ok(num(23), False))
#
#     def test_add(self) -> None:
#         self.assertFalse(self.guidance.ok(Sum(), True))
#         self.assertFalse(self.guidance.ok(Sum(), False))
#
#
# def try_match(rule: CompositeExpression, target: Expression,
#               direction: Direction,
#               dummies: Optional[FrozenSet[Variable]] = None,
#               definitions: Optional[FrozenSet[Variable]] = None) -> Set[
#     Expression]:
#     if dummies is None:
#         dummies = frozenset()
#
#     if has_head(rule, ForAll):
#         return try_match(
#             rule[1],
#             target,
#             direction,
#             dummies.union(rule.get_variables(dummies)),
#             definitions,
#         )
#
#     if definitions is None:
#         definitions = frozenset()
#
#     if has_head(rule, Exists):
#         # I guess we need another argument to this function, for definitions?
#         # The idea is that we gensym a witness, add definition to list of
#         # definitions, then can recurse.]
#         return try_match(rule[1],
#                          target,
#                          direction,
#                          dummies,
#                          definitions.union(rule.get_variables(
#                              definitions.union(dummies))))
#
#     # For now, only implement for ==.
#     assert has_head(rule, Equal)
#
#     assert dummies.isdisjoint(target.bound_variables())
#     assert dummies.isdisjoint(target.free_variables(frozenset()))
#
#     assert definitions.isdisjoint(target.bound_variables())
#     assert definitions.isdisjoint(target.free_variables(frozenset()))
#
#     # Recursing on the rule, rather than the target, seems ... kind of
#     # desperate.  It's only in special cases that you can hope that you'll be
#     # able to make progress that way.
#     #
#     # So there are two ways to proceed.  Think of it purely formally, e.g.
#     # (= (+ x 7) 11) and how to manipulate that tree.  Or think of it more
#     # like a middle schooler: on the left you have x + 7 beads, on the right
#     # you have 11 beads, and you can add or subtract beads from both sides to
#     # try to get x alone.
#     #
#     # From
#     # https://bestedlessons.org/2019/04/04/9-excellent-middle-school-math-textbooks-with-solutions/
#     # in grade 7 they solve simple equations like x + 7 = 11 or 5y = 20 with
#     # "mental math," which seems to boil down to "it's obvious," with the
#     # reminder that division is the opposite of multiplication.
#
#     res = match_and_substitute(dummies, rule[1], rule[2], target)
#
#     assert False
#
#     return res
#
# class TestDecideOnAdditiveInverse(unittest.TestCase):
#     def setUp(self) -> None:
#         self.guidance = Guidance()
#
#     def test_stuff(self) -> None:
#         # We'll just focus on LHS for now.
#         #
#         # Simulate already having seen and solved x + 0 and x + 0 + 0
#         self.guidance.lhs.update({0, Sum})
#
#         premise = Parser.parse('x + 7')
#
#         self.assertEqual(self.guidance.not_matching(premise), num(7))
#
#         # So now we need to find the premises that we can match with "7".
#         print(try_match(additive_inverse_right, num(7), Direction.FORWARD))
#
#         self.assertTrue(False)
#
#         # for axiom in field_axioms:
#             # match isn't what we want.  It only matches at root, and doesn't
#             # know about implies, forall, etc.
#             #
#             # Maybe want try_rule(), at least for now?
#             # try_rule(axiom, num(7), Direction.FORWARD)
#

if __name__ == "__main__":
    unittest.main()
