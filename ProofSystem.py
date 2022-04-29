"""A proof assistant, or interactive theorem prover.  This implements the
sequent calculus, including maintaining proof state such as context (the set
of symbols to the left of the turnstile) and goals.

Actually, I think the sequent calculus is implemented in MatchAndSubstitute's
try_rule(), along with some rules.  Hmm.  For example, "forall P, Q, P & Q -> P"
could be a rule, although that's a second order logic rule I think.

So in Hilbert-style deductive systems, it is common to have only modus ponens
and universal generalization as rules of inference, however, you then have
axiom schemas that encompass the rest of propositional logic.  Coq has
tactics like "split" for conjunction goals, and "left" and "right" for
disjunction goals.

Basic deduction functions used by most / all search techniques.

This file contains basic stuff that should be independent of any
particular search technique.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, Sequence, Iterator

from Expression import Expression, CompositeExpression
import MatchAndSubstitute
from MatchAndSubstitute import is_rule, Direction, is_equality

# from pprint import pprint
from typing import Optional, Union
from typing import TypeVar

# Python typing is such a shit show.
#
# https://docs.python.org/3/library/collections.abc.html#collections-abstract-base-classes
#
# "Collection" supports len(), contains and iter().
# "Sequence" supports random access through getitem.
#
# operator "+" doesn't support Sequence, and my code is cleaner using it.  So, I
# explicitly use "list" as a return type everywhere just so I can use "+".  The
# alternative is "temp = [x for x in first_seq]; temp.extend(second_seq); return
# temp."

# Wish I could make this a NamedTuple, but recursively typed NamedTuples and
# mypy are currently broken, see https://github.com/python/mypy/issues/3836
# class ExprAndParent(NamedTuple):
#    expr: Expression
#    parent: 'ExprAndParent'


class ExprAndParent:
    _expr: Expression
    _parent: Optional[ExprAndParent]

    def __init__(self, expr: Expression, parent: Optional[ExprAndParent]) -> None:
        self._expr = expr
        self._parent = parent

    @property
    def expr(self) -> Expression:
        return self._expr

    @property
    def parent(self) -> Optional[ExprAndParent]:
        return self._parent

    def __repr__(self) -> str:
        return repr(self._expr) + " & parent"


def collect_path(start: ExprAndParent) -> list[Expression]:
    ret: list[Expression] = []
    current: Optional[ExprAndParent] = start
    while current is not None:
        ret.append(current.expr)
        current = current.parent
    return ret


EAndP = TypeVar("EAndP", bound=ExprAndParent)


# This implements a Natural Deduction style inference engine.
# https://en.wikipedia.org/wiki/Natural_deduction
#
# Hilbert style was used in Principia Mathematica and is too hard to work
# with in practice.
#
# Instead, we use Fitch-style calculus
# https://en.wikipedia.org/wiki/Fitch_notation
#
# (Gentzen style seems to be all the rage, but Fitch seems more natuarl to me.)
#
# Essentially, every time we introduce a new assumption, we want to create a
# new object that holds that assumption in it's context, then we drive
# whatever we want in that object, then we can conclude "assumption => what
# we derived" in the parent object.
#
# How to do simplification?  There's no single goal expression that we can ==
# against to tell if we're done.  Also, this class kind of assumes all
# context items are propositions, not expressions of type math object.

# I think I was abstracting this from BruteForceProofState.
class ProofState:
    # Things equivalent to what we're trying to prove.  Proving any one of
    # these means we're done with our proof.
    goals: Mapping[Expression, EAndP]

    # Things that follow from our assumptions.  If we can derive a goal from
    # any of these, we're done.
    context: Mapping[Expression, EAndP]

    # Definitions of terms, introduced by substituting a generic witness for
    # an existential qualifier.
    definitions: Mapping[str, Expression]

    _parent: Optional[ProofState]

    verbosity: int

    def __init__(self, parent: Optional[ProofState], verbosity: int):
        self.verbosity = verbosity
        self._parent = parent


# TODO: I feel like this shouldn't be a separate class, but can somehow
# naturally be handled in ProofState.  So, TODO is to generalize this.
class SimplifyObject:
    # Propositions, as given to us.  Hopefully a small set.
    assumptions: Mapping[Expression, ExprAndParent]

    # Propositions that follow from our assumptions.
    context: Mapping[Expression, ExprAndParent]

    start: Expression

    # Simplifications of start, on the path
    simplifications: MutableMapping[Expression, ExprAndParent]

    verbosity: int

    def __init__(
        self, start: Expression, assumptions: Sequence[Expression], verbosity: int
    ):
        self.assumptions = {e: ExprAndParent(e, None) for e in assumptions}
        self.start = start
        self.verbosity = verbosity
        self.context = {}
        self.simplifications = {}

    def add_simplification(self, expr: ExprAndParent):
        self.simplifications[expr.expr] = expr


class Exprs(Mapping[Expression, EAndP]):
    """Mutable collection of ExprAndParent subclasses.  Given an Expr (that
    you just generated), can tell you whether it's already been generated,
    and gives you the ExprAndParent.  Also allows you to iterate over the
    exprs."""

    _exprs_map: MutableMapping[Expression, EAndP]
    _parent: Optional[Exprs[EAndP]]
    _exprs_rules: list[EAndP]
    _exprs_non_rules: list[EAndP]

    def __init__(
        self, exprs: Sequence[EAndP], parent: Optional[Exprs[EAndP]] = None
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

    def __contains__(self, expr: Expression) -> bool:  # type: ignore
        """Used to tell whether or not we've generated this expr before,
        so always checks all parents as well as itself."""
        return bool(expr in self._exprs_map or (self._parent and expr in self._parent))

    def __getitem__(self, key: Expression) -> EAndP:
        if key in self._exprs_map:
            return self._exprs_map[key]
        if self._parent is None:
            raise KeyError
        return self._parent[key]

    # Used to iterate over all expressions, to see if a newly generated
    # expression is an instance of any of them, meaning the proof is done.
    def __iter__(self) -> Iterator[Expression]:
        return [expr.expr for expr in self.all_exprs()].__iter__()

    def __len__(self) -> int:
        return len(self._exprs_map) + (len(self._parent) if self._parent else 0)

    def __repr__(self) -> str:
        return "\n".join(str(expr) for expr in self)

    def immediate_rules(self) -> Sequence[EAndP]:
        return self._exprs_rules

    def immediate_non_rules(self) -> Sequence[EAndP]:
        return self._exprs_non_rules

    def all_rules(self) -> list[EAndP]:
        if self._parent:
            return self._parent.all_rules() + self._exprs_rules
        else:
            return self._exprs_rules

    def all_exprs(self) -> list[EAndP]:
        # This won't work in general, because when we add a rule, it will change
        # the index of all elements of exprs_list.  Oi.
        return (
            self._exprs_non_rules
            + self._exprs_rules
            + (self._parent.all_exprs() if self._parent else [])
        )

    def equalities(self) -> list[EAndP]:
        parent_equalities = self._parent.equalities() if self._parent else []
        return [
            rule for rule in self._exprs_rules if is_equality(rule.expr)
        ] + parent_equalities


# BruteForceProofState, since it matches against all targets, is really part
# of a brute force setup, so isn't as general or independent as we'd like.  So
# maybe should be moved to a different Python file.

# Why do Exprs and BruteForceProofState both have parents?  I think they must
# point to the same thing, i.e. BruteForceProofState._parent.context ==
# BruteForceProofState.context._parent.


class BruteForceProofState:
    goals: Exprs[EAndP]
    context: Exprs[EAndP]
    # This really needs to be a list, mapping variable to expression that
    # defines it.
    definitions: Exprs[EAndP]
    _parent: Optional["BruteForceProofState"]
    verbosity: int

    def __init__(
        self,
        context: Sequence[ExprAndParent],
        goals: Sequence[ExprAndParent],
        parent: Optional["BruteForceProofState"],
        verbosity: int,
    ) -> None:
        self.verbosity = verbosity
        self._parent = parent

        self.context = Exprs(context, getattr(parent, "context", None))
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
        """Determines whether move equals or is_instance any element of targets.

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
        self, rule: Expression, expr_and_parent_in: ExprAndParent, direction: Direction
    ) -> Union[bool, Sequence[Expression]]:
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

            # Ideally, in the case of "P in B -> P * M == M * P," we'd
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
        self, non_rules: Sequence[EAndP], rules: Sequence[EAndP], direction: Direction
    ) -> Union[bool, Sequence[Expression]]:
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
