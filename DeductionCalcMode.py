from collections import defaultdict
from collections.abc import Mapping
from typing import Optional, Sequence, Union, cast

# from typing import Sequence
from Expression import CompositeExpression, Expression, Node
import MatchAndSubstitute
from MatchAndSubstitute import Direction, is_rule
from ProofSystem import ExprAndParent, Exprs, collect_path


class DistanceExprAndParent(ExprAndParent):
    _distance: int

    def __init__(
        self, expr: Expression, parent: Optional["DistanceExprAndParent"], distance: int
    ) -> None:
        super().__init__(expr, parent)
        self._distance = distance

    def __repr__(self) -> str:
        return f"{self._expr} ({self._distance}) & parent"


def parts(source: Expression) -> Mapping[Node, int]:
    if isinstance(source, Node):
        return {source: 1}

    result: Mapping[Node, int] = defaultdict(int)
    assert isinstance(source, CompositeExpression)
    for child in source:
        for key, value in parts(child).items():
            result[key] += value

    return result


def missing(
    source: Expression, desired_subexpression: Expression
) -> Mapping[Node, int]:
    # For now, we just count the type of each node in desired_subexpression,
    # and return how many of each type that we're missing.
    #
    # So basically we collapse all CompositeExpressions into a multiset.  Ok,
    # let's give it a try.

    source_parts = parts(source)

    result: Mapping[Node, int] = defaultdict(int)
    for part, count in parts(desired_subexpression).items():
        if part in source_parts:
            diff = count - source_parts[part]
            if diff > 0:
                result[part] = diff
        else:
            result[part] = count

    return result


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
    equivalents: Exprs[DistanceExprAndParent]
    desired_subexpression: Expression
    verbosity: int

    def __init__(self, desired_subexpression: Expression, verbosity: int):
        self.verbosity = verbosity
        self.desired_subexpression = desired_subexpression
        self.equivalents = Exprs([], None)

    def try_rule(
        self, rule: Expression, target: DistanceExprAndParent
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
            move_and_parent = target.__class__(
                move, target, sum(missing(move, self.desired_subexpression).values())
            )
            print(move_and_parent)

            if has_subexpression(move, target.expr):
                return list(reversed(collect_path(move_and_parent)))

            self.equivalents.add(move_and_parent)
            added = True

        return added
