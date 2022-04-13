# A runner for learning from high school algebra

import Parser
from Expression import (
    Expression,
    CompositeExpression,
    var,
    forall,
    exists,
    ExpressionType,
)
import DeductionApril2018
from typing import Sequence

# Save some typing
OBJECT = ExpressionType.OBJECT

# Need to implement a deduction class for "calc mode."


def ex(st: str) -> Expression:
    return Parser.parse(st)


def doit() -> None:
    a = var("a", OBJECT)
    b = var("b", OBJECT)
    c = var("c", OBJECT)

    # Group Axioms
    associativity: CompositeExpression = forall(
        {a, b, c}, ex("(a + b) + c == a + (b + c)")
    )

    commutativity: CompositeExpression = forall({a, b}, ex("a + b == b + a"))

    identity: CompositeExpression = forall(a, ex("0 + a == a"))

    # So Lean proposes an alternative:
    # exists(negative, forall(a, ex("a + negative(a) == 0")))
    # Which means we need to add function types.  In fact, as stated,
    # we'd need to add "sorts" to our language too, so we can distinguish
    # between "exists x in Real" vs "exists f in Real -> Real".  So maybe
    # treat negative as constant for now?  Then we simply say:
    # forall(a, ex("a + negative(a) == 0"))
    inverse: CompositeExpression = forall(a, exists(b, ex("a + b == 0")))

    group_axioms = [associativity, commutativity, identity, inverse]

    def helper(
        context: Sequence[Expression],
        goal: Expression,
        general_rules: Sequence[Expression],
        verbosity: int = 1,
    ) -> None:
        proof = DeductionApril2018.try_rules(context, goal, general_rules, verbosity)

        if not proof:
            print("*****  NO SOLUTION!  *****")
            exit(1)

        print("*****  Found solution!  *****")
        for step in proof:
            print(step)

    helper([], ex("x + 0 == x"), group_axioms, 100)


doit()
