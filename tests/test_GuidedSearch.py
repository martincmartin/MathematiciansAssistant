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

x = var('x', OBJECT)

additive_inverse_right: CompositeExpression = \
    forall(a, exists(b, ex("a + b == 0")))

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
    additive_inverse_right,
    forall(a, exists(b, ex("b + a == 0"))),
    forall(a, implies(ex("a != 0"), exists(b, ex("a * b == 1")))),
    forall(a, implies(ex("a != 0"), exists(b, ex("b * a == 1")))),

    # distributive
    forall((a, b, c), ex("a * (b + c) == a * b + a * c")),

    # Do I need to add 1 != 0?
]


class TestGuidedSimplify(unittest.TestCase):
    def test_x_plus_0(self):
        gs = GuidedSimplify(field_axioms, ex('x + 0'))

        # Start by iterating over all rules, and trying to apply them at
        # every spot in an expression.

        success = gs.brute_force(x)
        if success:
            print('SUCCESS!!')

        # Attempt number two.  Really should separate out proof state from
        # learning.  Oh well.
        gs._start = ex('(x + 0) + 0')
        gs.brute_force(x)

        gs._start = ex('0 + x')
        gs.brute_force(x)

        gs.solveme(ex('7 - 7'), num(0))
        gs.brute_force(x)
        # Next up: simplify 7 - 7.
        #
        # How do we define subtraction?  forall(x, y){x - y = x + -y} but we
        # don't have a unary minus, instead we have:
        # forall(x) exists(a) x + a = 0.
        # In the definition of -, how do we say "the one from the additive
        # inverse rule?"  I suppose we don't even know that the additive
        # inverse is unique until we prove it.
        #
        # forall(x, y) exists(a) {y + a = 0 and x - y = x + a}
        #
        # substitute in x = y = 7:
        #
        # exists(a) {7 + a = 0 and 7 - 7 = 7 + a}
        #
        # Get a witness for a, and first conjunct to premises, use second
        # conjunct to reduce 7 - 7 to 7 + a, then first conjunct to 0.
        #
        # Ugh, a lot of work.
        #
        # And this doesn't let us simplify 7 - 5.
        #
        # forall(x, y, z){x - y = z <=> x = z + y}
        #
        # Substitute in 7 & 7:
        #
        # forall(z){7 - 7 = z <=> 7 = z + 7}
        #
        # By additive identity, 0 + 7 = 7, therefore 7 - 7 = 0.  And we
        # didn't need existence of additive inverse.  Although we're kind of
        # sneaking in the fact that subtraction is well defined, i.e. that
        # there's a unique value for x - y.  Because if we prove a = x - y,
        # and x - y = b, then by substitution we have a = b.

        # I think I'm on my own for how to define functions.  Coq has
        # Fixedpoint, which must have a decreasing argument.  Not sure how a
        # general function is defined.  But basically, in math you have to
        # show the output is unique, and maybe characterize the domain?  Or
        # you can use a relation.  If we define subtraction as a relation,
        # what does that look like?

        # From a question I asked here:
        # https://coq.discourse.group/t/defining-mathematical-function-implicitly/1238/2
        #
        # "If you want to define a function, there is essentially no way
        # around fixpoints."
        #
        # Proving "forall x, exists y, R x y", in constructive logic,
        # shows how to construct a y given an x.  Hopefully equivalent to
        # Fixedpoint, in Coq.

        # S(x, y, z) iff x = z + y.  Prove that forall{x, y}exists{z} such
        # that x = z + y, and that if z1 & z2 satisfy that, then z1 = z2.
        # Then ... I don't know.  I guess we're trying to find z for S(7, 7,
        # z).  I guess we express x + (7 - 7) as exists{z}(S(7, 7, z) and x +
        # z).  Which has root exists, which makes it look like a proposition.

        # Could just provide axioms about subtraction, i.e. that x - y = z
        # iff x = z + y.

        # In Lean "as far as I know, even if you have a proof of unique
        # existence, this classical.some is still the only way to "produce" a
        # function"
        # https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Going.20from.20.22exists.20unique.22.20to.20a.20function
        # Well, I want to capture classical reasoning anyway, so maybe this
        # is ok.
        #
        # Lean books:
        #
        # "Theorem Proving in Lean": Learning Lean itself.
        # "Logic and Proof": Textbook on math logic using Lean
        # "Programming in Lean": an introduction and a reference manual for programming in Lean


        print('**********  Can now solve')
        for start, rule in gs.algorithms.items():
            print(f'{start}    using {rule}')

        self.assertTrue(False)


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

if __name__ == '__main__':
    unittest.main()
