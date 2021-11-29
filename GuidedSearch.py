# Need to represent "set of solvable expressions."
#
# For now, we'll use something too simple, and iterate later.

from __future__ import annotations

from collections.abc import MutableMapping

from Expression import Variable, NumberLiteral, Node, Expression,\
    CompositeExpression
from typing import cast, Optional

from MatchAndSubstitute import try_rule, Direction, is_rule, match


class Guidance:
    def __init__(self):
        self.lhs = set()  # Handle "x" allowed on LHS in code.
        self.rhs = {NumberLiteral}

    # Distance by itself isn't too useful, we need to know what needs to
    # change and what doesn't, e.g. we need a list of edits.  Edit distance
    # might be helpful in choosing between options, e.g. when selecting a
    # premise to turn into the goal, consider them in order of edit distance.
    # But for now, let's just look at which nodes are allowed & not allowed.
    #
    # Actually, we have no way to express that "x" is required on LHS,
    # just that it's allowed.  Oh well.
    def ok(self, node: Node, lhs: bool) -> bool:
        recognized = self.lhs if lhs else self.rhs
        if type(node) in recognized:
            return True
        # For now, hack that LHS can contain 'x'.
        return lhs and isinstance(node, Variable) and node.name == 'x'

    def not_matching(self, other: Expression) -> Optional[Node]:
        if isinstance(other, Node):
            if self.ok(other, True):
                return None
            return other
        other = cast(CompositeExpression, other)
        for subexpr in other:
            x = self.not_matching(subexpr)
            if x:
                return x
        return None

# So now, I need to take a goal, find which nodes I need to get rid of.  Then
# find a rule which addresses those nodes.
#
# Actually, maybe I can classify each rule for what it can add or get rid of.
# For example, a + 0 == a can get rid of (or introduce) + & 0, whereas a * 0
# == 0 can get rid of (or introduce) * and arbitrary subexpression,
# but requires pre-existing zero.
#
# Associativity and commutativity add and get rid of nothing, so are invisible
# to this framework.  Same with distributive, it turns 1 copy into 2 (or vice
# versa), but doesn't change the presence / absence of any feature.
#
# Also, we can't just have a notion of "all forms we can solve right now,"
# because once in that form, we need to continue with the previously known
# steps to actually get the answer.  So it's really more like, "if it's of
# this form, apply this algorithm."  Algorithms can use other algorithms as
# subroutines I guess.
#
# I suppose we could express them as rules?  i.e. the same way we express
# "a + 0 == a", we could express "x + 7 == 11 <=> x == 11 - 7," or "x + a ==
# b <=> x == b - a."  But how do we express a rule like "x with any number of
# 0s and +s"?  Do we need a concept like summation notation? First we need a
# concept like "sum but the order doesn't matter."  How do we express that,
# when all we have is a binary operator?  It could recognize that
# a + (b + c) == (a + b) + c, then all the combinations with 4, then with 5.
# Then it could hypothesize that all the combinations with n are the same.
# Then it could prove that inductively.
#
# So let's work on that.  Do we give it the concept of a list, or does it
# figure that out on its own?  It's not even clear how you'd express it.
# You want to say something like "all ways of combining + and these elements
# in this order," but of course "these elements in this order" is exactly a
# list.  Maybe you use an element of the equivalence class, e.g. the list [a,
# b, c, d] could be represented as a + ((b + c) + d), or any other
# combination you can get to from there using just associativity.  Also
# doesn't quite help with "what forms can I solve?" where you need to
# be able to recognize the form of the expression.
#
# So we're trying to discover & represent a single x along with any
# combination of + and zero.  It really needs the concept of set, or list,
# or function, or something.
#
# What does the inductive proof look like?  We need a statement like "any
# combination of 0 & +, along with a single x."  We can define that
# recursively, e.g. "an XPlusZeros expression is either x, or an xPlusZeros
# expression + 0, or 0 + an XPlusZeros expression."  Which is great for
# proofs but doesn't help with understanding or recognizing it, or telling
# how far away we are from one.  We could derive properties from that I
# suppose, like the number of possible zeros (any natural number) or the
# number of xs (always exactly 1).
#
# Well, there's also the concept of list from function.  A list is
# essentially a sequence, so a mapping from 1 .. n -> numbers.  Might be
# awkward to work with though.


# So what we're doing here:
#
# We give it some examples like x + 0 + 0, and it notices that it is applying
# additive identity twice.  Maybe now, maybe later, it decides to generalize
# this to "a single x with any number of zeros joined by +s."
#
# The next problem (in dragonbox) is 7 + -7 + x + 11 + -11.  Then 8 + -4 + x +
# 4 + -8.
#
# When presented with 7 + x == 11, we want it to consider a goal of 0 + x for
# the LHS.  Or at least, when it looks at what rules it can use with 7,
# and it finds additive inverse, it recognizes that the result will involve 0
# and x, and it knows how to solve that.
#
# So one possibility is "definition with properties," i.e. the XPlusZeros
# thing above is exact, then you derive properties from it, e.g. "expression
# contains 1 or more zeros" and "all operators are +s", that sort of thing.
# A regex like matching would be even more powerful, but could come later.
#
# So let's say it doesn't generalize, and it can only solve x + 0 and (x + 0)
# + 0.  Now it's given x + 7.  What does it do?  Realizes the 7 is blocking
# it.  Looks for ways to manipulate the 7.  Sees 7 * 7^-1 == 1, but 1 would
# also be a problem.  Sees distributive & commutative laws for both + and *,
# they won't change the 7. Additive and multiplicative identity would need 7
# for a, so won't change the 7.  Distributive might change the number of 7s,
# but not the presence / absence of 7s.  So of all of those, additive
# identity seems most useful.
#
# So we need to code up "realize 7 is blocking it" and "look for how rules
# would affect 7", look at the subset that will eliminate the 7, and of
# those, one produces a 1, the other produces a 0.  And recognize that 0 is
# in the set of things we can already solve.
#
# For "realize 7 is blocking it," this is where we compare the properties of
# the expression with the properties of set of things we can solve: x is in
# there, + is in there, but 7 isn't in there.  Simple for now.  Could also be
# done by looking at how a structural match fails, e.g. when matching x + 7
# with x + 0, the x and the + match, but the 7 fails.  But let's stick with
# properties for now.

class GuidedSimplify:
    _start: Expression
    # Map from expressions we can simplify, to rule used to perform the
    # simplification.
    _algorithms: MutableMapping[Expression, Expression]

    def __init__(self, rules, start: Expression):
        self._rules = rules
        self._start = start
        self._algorithms = {}

    @property
    def rules(self):
        return self._rules

    @property
    def start(self):
        return self._start

    @property
    def algorithms(self):
        return self._algorithms

    def solved(self, start: Expression, rule: Expression):
        print(f'{start} SOLVED BY {rule}!')
        self._algorithms[start] = rule

    def solveme(self, start: Expression, goal: Expression):
        self._start = start
        return self.brute_force(goal)

    # Use this to find which rule(s) simplify the start expression.
    def brute_force(self, goal):
        rules_to_use = set()
        for rule in self._rules:
            if not is_rule(rule):
                continue
            results = try_rule(rule, self._start, Direction.FORWARD)
            for result in results:
                print(f'{result} from {rule}')
                if result == goal:
                    self.solved(self._start, rule)
                    return True
                for known, next_rule in self._algorithms.items():
                    subs = match({}, known, result)
                    if subs is not None:
                        self.solved(self._start, rule)
                        return True
        return False

    # Now we realize we can solve x + 0, using additive_identity.  We have to
    # realize that we can't solve x + 0 + 0 yet, but when we see it, we can
    # use additive identity to turn it into something we can solve.  Hmm.
    # Maybe for now, just have a list of literal expressions we can solve.

