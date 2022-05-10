from collections import defaultdict
from collections.abc import Mapping
from typing import Sequence, Union

# from typing import Sequence
from Expression import CompositeExpression, Expression, Node
import MatchAndSubstitute
from MatchAndSubstitute import Direction, is_rule
from ProofSystem import ExprAndParent, Exprs, collect_path


def parts(source: Expression) -> Mapping[Expression, int]:
    if isinstance(source, Node):
        return {source: 1}

    result: Mapping[Expression, int] = defaultdict(int)
    assert isinstance(source, CompositeExpression)
    for child in source:
        for key, value in parts(child).items():
            result[key] += value

    return result


def distance(source: Expression, desired_subexpression: Expression) -> int:
    # For now, we just count the type of each node in desired_subexpression,
    # and return how many of each type that we're missing.
    #
    # So basically we collapse all CompositeExpressions into a set.  Ok, let's
    # give it a try.

    source_parts = parts(source)

    total = 0

    for part, count in parts(desired_subexpression).items():
        if part in source_parts:
            total += max(count - source_parts[part], 0)
        else:
            total += count

    return total


def has_subexpression(expr: Expression, subexpr: Expression) -> bool:
    """
    True if subexpr exists inside expr.  False if not.
    """
    if expr == subexpr:
        return True
    if isinstance(expr, CompositeExpression):
        for child in expr:
            if has_subexpression(child, subexpr):
                return True
    return False


class DeductionCalcMode:
    equivalents: Exprs[ExprAndParent]
    target: Expression
    verbosity: int

    def __init__(self, verbosity: int):
        self.verbosity = verbosity
        self.equivalents = Exprs([], None)

    def try_rule(
        self, rule: Expression, target: ExprAndParent, current_distance: int
    ) -> Union[bool, Sequence[Expression]]:
        assert isinstance(rule, CompositeExpression)
        assert is_rule(rule)

        exprs = MatchAndSubstitute.try_rule(
            rule, target.expr, Direction.FORWARD, allow_trivial=True
        )
        # if exprs:
        print(f"try_rule: {rule} transformed {target} into {exprs}")

        added = False
        for move in exprs:
            if move in self.equivalents:
                continue
            move_and_parent = target.__class__(move, target)

            if has_subexpression(move, target.expr):
                return list(reversed(collect_path(move_and_parent)))

            self.equivalents.add(move_and_parent)
            added = True

        return added


def transform_to_subexpression(
    start: Expression, desired_subexpression: Expression, rules: Sequence[Expression]
):
    start_distance = distance(start, desired_subexpression)

    for rule in rules:
        try_rule(rule, start, start_distance)
