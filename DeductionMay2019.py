# Trying to solve simple algebra problems like "2 * x + 3 == 13, find x."

from Expression import Expression, var, forall
from DeductionHelpers import ExprAndParent, Exprs
import MatchAndSubstitute
from MatchAndSubstitute import Direction

from typing import Sequence

import Parser

# Given an expression and a set of rules, apply the rules.


def learn_rules(
        start: Expression,
        rules_in: Sequence[Expression],
        verbosity: int = 0,
) -> None:
    rules = [ExprAndParent(r, None) for r in rules_in]

    # Try each rule
    for rule in rules:
        if verbosity >= 10:
            print("Rule: "+str(rule.expr))

        print(MatchAndSubstitute.try_rule(rule.expr, start, Direction.FORWARD))


def ex(st: str) -> Expression:
    return Parser.parse(st)

def doit() -> None:
    a = var("a")
    x = var("x")
    # How should we represent the rules about doing the same thing to both
    # sides of an equation?  For now, I suppose just list them separately,
    # one for each operation?  Should be able to deduce them from reflexivity
    # of equals, i.e. since forall a, a == a, then substitute x * r for a.
    # But, later.
    #
    # However, that's not very useful.  I guess we specifically want to
    # multiply by 1/2, or perhaps a better way to put it, divide both sides
    # by 2.  We do that because there's a 2 * at the top of the equation.
    # Hmm.  This reasoning is getting very specific to simple formula I have.
    mult_eqn = forall( (a, x), ex("x * a == x * a"))
    learn_rules(ex("2 * x == 10"), [mult_eqn], 20)

doit()