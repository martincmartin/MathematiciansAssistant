"""Pattern matching and substitution functions on Expressions.

Lowest level building blocks of deduction.
"""

from Expression import *
from typing import *
import enum as _enum


def match(
    dummies: AbstractSet[Variable], pattern: Expression, target: Expression
) -> Optional[Mapping[Variable, Expression]]:
    """Matches "pattern" against "target"s root, i.e. not recursively.

    This is a very simple, structural match.  It doesn't know anything about
    implies, forall, etc.  Its a simple destructuring bind, where "dummies"
    are the nodes that count as variables.

    "dummies" is the set of Nodes in "pattern" that can match any sub
    expression.

    Returns the substitution, as dict, that makes them match, or None if there's
    no match.  Be careful: both the empty dict (meaning there's a match that
    works with any substitution) and None (they don't match no matter what you
    substitute) evaluate as false in Python.
    """

    assert isinstance(target, Expression)

    if isinstance(pattern, Node):
        if pattern in dummies:
            pattern = cast(Variable, pattern)
            assert pattern not in target.free_variables(dummies)
            # This is a hack until we have types: assume any composite
            # expression is boolean valued.  Also, assume variables don't
            # match operators.
            if isinstance(target, Node):
                # If target is anything other than a variable or number literal,
                # don't match.
                if not (
                    isinstance(target, NumberLiteral)
                    # or target.free_variables(set())):
                    or isinstance(target, Variable)
                ):
                    return None
            return {pattern: target}
        if pattern == target:
            return {}
        return None

    pattern = cast(CompositeExpression, pattern)

    # TODO: Allow something akin to *args, a pattern that matches any
    # number of remaining args.
    if isinstance(target, Node):
        return None
    target = cast(CompositeExpression, target)

    if len(pattern) != len(target):
        return None

    ret: MutableMapping[Variable, Expression] = {}
    for p, t in zip(pattern, target):
        subs = match(dummies, p, t)
        if subs is None:
            return None
        for vari, value in subs.items():
            if vari in ret:
                # TODO: Would like to do "equivalent" here, e.g. if +
                # is commutative, consider x + y the same as y + x.
                # This can do == on CompositeExpressions.
                if ret[vari] != value:
                    return None
        ret.update(subs)
    return ret


class Direction(_enum.Enum):
    FORWARD = _enum.auto()
    BACKWARD = _enum.auto()
    BOTH = _enum.auto()


def is_rule(expr: Expression) -> bool:
    """Predicate. returns True iff try_rule(expr, target, backwards) could
    return a non-empty set for some target, either forwards or backwards.
    """
    if has_head(expr, ForAll):
        return is_rule(cast(CompositeExpression, expr)[1])

    return has_head(expr, Implies) or has_head(expr, Equivalent) or has_head(
        expr, Equal
    )


def is_instance(
    expr: Expression, rule: Expression, dummies: FrozenSet[Variable] =
        frozenset()
) -> Optional[Mapping[Variable, Expression]]:
    """Determines whether 'expr' is an instance of 'rule.'

    returns the substitution that makes them match, or None if there's no match.

    Basically a wrapper on 'match'.  In fact, perhaps 'match' should be
    merged into this.

    NOTE: Doesn't handle ForAll that's under anything other than more ForAlls.
    """

    if has_head(rule, ForAll):
        rule = cast(CompositeExpression, rule)
        return is_instance(
            expr, rule[1], dummies.union(rule.get_variables(dummies))
        )

    return match(dummies, rule, expr)


def try_rule(
    rule: Expression, target: Expression, direction: Direction
) -> Set[Expression]:
    """Apply "rule" to "target", returns any new expressions it generates.

    If rule is Implies, only applies it to "target"'s root.  If rule is
    Equivalent or Equal, applies it recursively.

    Returns a possibly empty set() of transformed expressions.
    """
    if str(rule) == "P * M == M * P":
        print("OMG")

    return _try_rule_recursive(frozenset(), rule, target, direction)


def _try_rule_recursive(
    dummies: FrozenSet[Variable],
    rule: Expression,
    target: Expression,
    direction: Direction,
) -> Set[Expression]:
    """Apply "forall(dummies, rule)" to "target", return generated expressions.

    See try_rule() for more details.
    """
    assert is_rule(rule)
    rule = cast(CompositeExpression, rule)

    if has_head(rule, ForAll):
        # For "forall" we add the variables to dummies and recurse.
        # TODO: rename dummy if its in target.free_variables(dummies) or
        # dummies.
        return _try_rule_recursive(
            dummies.union(rule.get_variables(dummies)),
            rule[1],
            target,
            direction,
        )

    # Rename any variables now, so we don't need to worry about them when
    # calling *match_and_substitute below.
    quant = rename_quant(forall(dummies, rule), rule.bound_variables())
    dummies = quant.get_variables(frozenset())
    rule = quant[1]

    if has_head(rule, Implies):
        # For ==>, if we're working backwards from the conclusion, we see if we
        # can match the RHS, and if so, we return the LHS, with appropriate
        # substitutions and free variables.  If we're working forwards, we match
        # the LHS and substitue on the RHS.
        if direction == Direction.BACKWARD:  # type: ignore
            return _match_and_substitute(dummies, rule[2], rule[1], target)
        elif direction == Direction.FORWARD:  # type: ignore
            return _match_and_substitute(dummies, rule[1], rule[2], target)

    if has_head(rule, Equivalent) or has_head(rule, Equal):
        bound_in_target = target.bound_variables()
        if not dummies.isdisjoint(bound_in_target):
            # Should I rename dummies, or target?  Dummies
            # is probably less disruptive.
            temp = rename_quant(forall(dummies, rule),
                        bound_in_target)
            dummies = temp.get_variables(frozenset())
            rule = temp[1]

        return _recursive_match_and_substitute(
            dummies, rule[2], rule[1], target
        ).union(
            _recursive_match_and_substitute(dummies, rule[1], rule[2], target)
        )

    return set()


def _match_and_substitute(
    dummies: FrozenSet[Variable],
    antecedent: Expression,
    consequent: Expression,
    target: Expression,
) -> Set[Expression]:
    """Apply 'forall(dummies), antecedent ==> consequent' to target.

    i.e. if "antecedent" matches "target", then return consequent with
    appropriate substitutions.

    If match succeeds, returns a set with one element.  If if fails, returns
    an empty set.

    dummies: the set of variables in antecedent that will take on
    subexpressions of target, which will then be substituted in consequent.
    """

    subs = match(dummies, antecedent, target)
    if subs is not None:
        return {_substitute(subs, consequent)}
    return set()


def _recursive_match_and_substitute(
    dummies: AbstractSet[Variable],
    antecedent: Expression,
    consequent: Expression,
    target: Expression,
) -> Set[Expression]:
    """In "target", replaces any occurrence of antecedent with consequent.

    That is, apply 'forall(dummies) antecedent <==> consequent' to all
    subexpressions of target.

    Returns a (possibly empty) set().

    dummies: the set of variables in "antecedent" that will take on values in
    "target", and then be substituted into "consequent".
    """
    result = set()

    subs = match(dummies, antecedent, target)
    if subs is not None:
        result.add(_substitute(subs, consequent))

    if isinstance(target, Node):
        return result

    target = cast(CompositeExpression, target)

    if has_head(target, Quantifier):
        quant_vars = target.get_variables(frozenset())
        free_vars = antecedent.free_variables(set()).union(
            consequent.free_variables(set())
        )
        if not free_vars.isdisjoint(quant_vars):
            # First, if its a dummy that collides, rename that, since they
            # won't appear in the result anyway.
            assert dummies.isdisjoint(quant_vars)
            # if not dummies.isdisjoint(quant_vars):
            #     Hmm.  dummies might be used above us.  Let's do this outside'
            #     the recursive call.
            #     forall(dummies, equivalent(antecedent, consequent))
            #     antecedent = rename_variable(antecedent, dummies)
            #     consequent = rename_variable(consequent, dummies)

        free_vars = antecedent.free_variables(set()).union(
            consequent.free_variables(set())
        )

        if not free_vars.isdisjoint(quant_vars):
            target = rename_quant(target, free_vars)
            quant_vars = target.get_variables(frozenset())
        assert free_vars.isdisjoint(quant_vars)

    for index, expr in enumerate(target):
        all_changed = _recursive_match_and_substitute(
            dummies, antecedent, consequent, expr
        )
        for changed in all_changed:
            # new_target = target[:index] + (changed,) + target[index+1:]
            new_target = list(target)
            new_target[index] = changed
            result.add(CompositeExpression(new_target))
    return result


def _substitute(
    subs: Mapping[Variable, Expression], expr: Expression
) -> Expression:
    """Perform the substitutions given by subs on expr."""

    # What to do about unsubstituted dummies??  I guess just add a
    # ForAll at the front?  e.g. if you want to apply P ^ Q ==> Q backwards,
    # you're introducing a P.
    if isinstance(expr, Node):
        # Kind of ugly that this is special case.  Not sure how to fix that
        # though.
        if isinstance(expr, Quantifier):
            return expr.__class__(subs.get(v, v) for v in
                                  expr.get_variables_tree(frozenset()))

        return subs.get(cast(Variable, expr), expr)

    expr = cast(CompositeExpression, expr)

    # Actually, this does the wrong thing for quantifiers, since the quantified
    # over variable shadows any instance in what we're trying to substitute.
    # Hmm.
    # Should I just disallow shadowing?
    return CompositeExpression([_substitute(subs, e) for e in expr])

    # TODO: Handle "or" and "and", e.g. A <==> B should be the same as
    # A ==> B and B ==> A.
    #
    # In fact, A ==> B is the same as not A or B, suggesting that for
    # boolean expressions, if the taget is "B" and the rule is "A or
    # B", if the Bs match we can return substituted "not A" as a
    # possible predecessor.
    #
    # In fact, we could define "or" in terms of "==>" like this:
    #
    # \forall [P, Q], P or Q <==> (not P) ==> Q.
    #
    # I guess this is similar to Horn clauses, which treat ==> and
    # "and" as the building blocks.


def is_equality(expr: Expression) -> bool:
    """Predicate. returns True iff expr is a (possibly universally quantified)
    equality.
    """
    if has_head(expr, ForAll):
        return is_equality(cast(CompositeExpression, expr)[2])

    return has_head(expr, Equal)


def new_variable(old_variable: Variable, taken: Set[Variable]) -> Variable:
    taken_names = {t.name for t in taken}
    new_name = old_variable.name
    while new_name in taken_names:
        new_name = "_" + new_name
    return var(new_name)


def get_lhs(expr: Expression) -> Expression:
    assert is_equality(expr)
    while has_head(expr, ForAll):
        expr = cast(CompositeExpression, expr)
        # Need to do something with the variables here.  Hmm.  Maybe this is
        # why logic traditionally has the concept of free vs bound variables?
        expr = expr[2]
    assert has_head(expr, Equal)
    expr = cast(CompositeExpression, expr)
    return expr[1]


def rename_quant(
    quant: CompositeExpression, taken: Set[Variable]
) -> CompositeExpression:
    """Given a quantified expression, renames any variables that are in "taken"."""
    assert has_head(quant, Quantifier)

    return cast(CompositeExpression, _rename_variables(quant.get_variables(
        frozenset()), taken, quant))


def _rename_variables(to_rename: AbstractSet['Variable'], taken: Set[Variable],
                     expr: Expression) -> Expression:
    to_rename = taken.intersection(to_rename)
    if not to_rename:
        return expr

    # Decide on new variable names.
    subs = {old_name: new_variable(old_name, taken) for old_name in to_rename}
    return _substitute(subs, expr)
