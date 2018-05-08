"""Basic deduction functions used by most / all search techniques.

This file contains basic stuff that should be independent of any
particular search technique.
"""

from Expression import Expression, CompositeExpression
import MatchAndSubstitute
from MatchAndSubstitute import is_rule, Direction, is_equality

# from pprint import pprint
from typing import List, Mapping, Dict, Sequence, Iterator
from typing import Optional, Union
from typing import TypeVar

# Wish I could make this a NamedTuple, but recursively typed NamedTuples and
# mypy are currently broken, see https://github.com/python/mypy/issues/3836
# class ExprAndParent(NamedTuple):
#    expr: Expression
#    parent: 'ExprAndParent'


class ExprAndParent:
    _expr: Expression
    _parent: "ExprAndParent"

    def __init__(self, expr: Expression, parent: Optional["ExprAndParent"]) -> None:
        self._expr = expr
        self._parent = parent

    @property
    def expr(self) -> Expression:
        return self._expr

    @property
    def parent(self) -> "ExprAndParent":
        """Return type should really be the actual (derived) class of self."""
        return self._parent

    def __repr__(self) -> str:
        return repr(self._expr) + " & parent"


def collect_path(start: ExprAndParent) -> List[Expression]:
    ret = []
    while start is not None:
        ret.append(start.expr)
        start = start.parent
    return ret


EAndP = TypeVar("EAndP", bound=ExprAndParent)


class Exprs(Mapping[Expression, EAndP]):
    """Mutable collection of ExprAndParent subclasses.  Given an Expr (that
    you just generated), can tell you whether it's already been generated,
    and gives you the ExprAndParent.  Also allows you to iterate over the
    exprs. """
    _exprs_map: Dict[Expression, EAndP]
    _parent: Optional["Exprs"]
    _exprs_rules: List[EAndP]
    _exprs_non_rules: List[EAndP]

    def __init__(
        self, exprs: Sequence[EAndP], parent: Optional["Exprs"] = None
    ) -> None:
        self._parent = parent
        self._exprs_non_rules = [e for e in exprs if not is_rule(e.expr)]
        self._exprs_rules = [e for e in exprs if is_rule(e.expr)]
        self._exprs_map = {
            expr.expr: expr for expr in self._exprs_non_rules + self._exprs_rules
        }

    def add(self, expr_and_parent: EAndP) -> None:
        if is_rule(expr_and_parent.expr):
            self._exprs_rules.append(expr_and_parent)
        else:
            self._exprs_non_rules.append(expr_and_parent)
        self._exprs_map[expr_and_parent.expr] = expr_and_parent

    def __contains__(self, expr: Expression) -> bool:
        """Used to tell whether or not we've generated this expr before,
        so always checks all parents as well as itself."""
        return bool(expr in self._exprs_map or (self._parent and expr in self._parent))

    def __getitem__(self, key: Expression) -> EAndP:
        if key in self._exprs_map:
            return self._exprs_map[key]
        return self._parent[key]

    # Used to iterate over all expressions, to see if a newly generated
    # expression is an instance of any of them, meaning the proof is done.
    def __iter__(self) -> Iterator[Expression]:
        return [expr.expr for expr in self.all_exprs()].__iter__()

    def __len__(self) -> int:
        return len(self._exprs_map) + (len(self._parent) if self._parent else 0)

    def __repr__(self) -> str:
        return "\n".join(str(expr) for expr in self)

    def immediate_rules(self) -> List[EAndP]:
        return self._exprs_rules

    def immediate_non_rules(self) -> List[EAndP]:
        return self._exprs_non_rules

    def all_rules(self) -> List[EAndP]:
        if self._parent:
            return self._parent.all_rules() + self._exprs_rules
        else:
            return self._exprs_rules

    def all_exprs(self) -> List[EAndP]:
        # This won't work in general, because when we add a rule, it will change
        # the index of all elements of exprs_list.  Oi.
        return self._exprs_non_rules + self._exprs_rules + (
            self._parent.all_exprs() if self._parent else []
        )

    def equalities(self) -> List[EAndP]:
        # Returns a List, rather than Sequence or Iterable, because Python
        # makes dealing with sequences slightly inconvenient: list's "+" only
        # takes other lists, not sequences.  So, concatenating a sequence
        # onto a list is done "temp = [ ... ]; temp.extend(seq); return
        # temp."  I'd rather have the clarity of just "return [ ... ] + seq".
        parent_equalities = self.parent.equalities() if self._parent else []
        return [
            rule for rule in self._exprs_rules if is_equality(rule._expr)
        ] + parent_equalities


# Why do Exprs and ProofState both have parents?  I think they must point to
# the same thing, i.e. ProofState._parent.context == ProofState.context._parent.


class ProofState:
    goals: Exprs[EAndP]
    context: Exprs[EAndP]
    _parent: Optional["ProofState"]
    verbosity: int

    def __init__(
        self,
        context: Sequence[ExprAndParent],
        goals: Sequence[ExprAndParent],
        parent: Optional["ProofState"],
        verbosity: int,
    ) -> None:
        self.verbosity = verbosity
        self._parent = parent

        # context and goals are actually not used in any method.  So this
        # class is more like a C++ struct than a class.  Yikes!
        self.context = Exprs(context, getattr(parent, "context", None))
        # Only the "brute force" constructor takes a second argument here,
        # which is I think why PyCharm is complaining.
        self.goals = Exprs(goals, getattr(parent, "goals", None))

    def _is_instance(self, expr: Expression, rule: Expression):
        """Wraps MatchAndSubstitute.is_instance to print if verbose."""
        subs = MatchAndSubstitute.is_instance(expr, rule)
        if self.verbosity > 0 and subs is not None:
            print(
                str(expr)
                + " is an instance of "
                + str(rule)
                + " subs "
                + str(subs)
                + "  !!!!!!"
            )
        return subs

    def _match_against_exprs(
        self, move: Expression, targets: Mapping[Expression, EAndP]
    ) -> Optional[EAndP]:
        """Determines whether move equals or is_instance any
        element of targets.

        If so, returns the element.  If not, returns None.

        From self, only uses verbosity.
        """
        if move in targets:
            return targets[move]

        return next(
            (
                targets[target]
                for target in targets
                if self._is_instance(move, target) is not None
            ),
            None,
        )

    def try_rule(
        self, rule: Expression, expr_and_parent_in: EAndP, direction: Direction
    ) -> Union[bool, List[Expression]]:
        """Applies "rule" to "expr_and_parent_in", updating self with
        generated expressions.

        A wrapper around MatchAndSubstitute.try_rule().

        If that finishes the proof, returns path from start to goal.
        Otherwise, adds the any expressions to context (if forward) or
        goals (if backward), and returns a bool as to whether or not it at
        least generated a new expression.
        """

        assert isinstance(rule, CompositeExpression)
        assert is_rule(rule)
        assert direction == Direction.FORWARD or direction == Direction.BACKWARD

        # For return type, could really use one of those "value or error" types,
        # so that if callers don't get the bool, they'll return right away too.
        already_seen: Exprs[EAndP]
        targets: Exprs[EAndP]
        if direction == Direction.FORWARD:
            already_seen = self.context
            targets = self.goals
        else:
            already_seen = self.goals
            targets = self.context

        exprs = MatchAndSubstitute.try_rule(rule, expr_and_parent_in.expr, direction)

        if self.verbosity >= 10 or (self.verbosity > 0 and exprs):
            print(
                f"try_rule: {rule} transformed {expr_and_parent_in.expr} into {exprs}"
            )

        added = False
        for move in exprs:
            if move in already_seen:
                continue

            move_and_parent = expr_and_parent_in.__class__(move, expr_and_parent_in)

            # Ideally, in the case of P in B -> P * M == M * P, we'd
            # recognize that the latter is equivalent to the former, and is
            # strictly more useful so we can get rid of the former.  But I
            # think that takes some global knowledge of the proof, e.g. that
            # "P in B" doesn't appear in the goal in any form, or in any
            # other premises, etc.  So we'll skip that for now.

            found = self._match_against_exprs(move, targets)
            if found:
                if direction == Direction.FORWARD:
                    return list(reversed(collect_path(found))) + collect_path(
                        move_and_parent
                    )
                else:
                    return list(reversed(collect_path(move_and_parent))) + collect_path(
                        found
                    )
            already_seen.add(move_and_parent)
            added = True

        return added

    # Should this go in a derived class, since its a (brute force) search
    # strategy?  Oh well.
    def try_all_rules(
        self, non_rules: List[EAndP], rules: List[EAndP], direction: Direction
    ) -> Union[bool, List[Expression]]:
        """calls try_rule() for each pair of rules and non_rules."""
        made_progress = False
        for cont in non_rules:
            if self.verbosity > 0:
                print("*** " + str(direction) + " ***  " + str(cont.expr))
            for rule in rules:
                if self.verbosity >= 10:
                    print("Rule: " + str(rule.expr))
                found = self.try_rule(rule.expr, cont, direction)
                if isinstance(found, bool):
                    made_progress = made_progress or found
                else:
                    return found
        return made_progress
