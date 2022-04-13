"""Pattern matching and substitution functions on Expressions.

Lowest level building blocks of deduction.

So try_rule implements modus ponens, i.e. if the rule is of the form P => Q,
then in the forward direction if the target is P, it returns Q; in backwards,
if the target is Q, it returns P.  In fact, it represents a generalized form
of it: forall{x1, ..., xn} P(x1, ..., xn) => Q(x1, ..., xn), it does pattern
matching with the target and does the substitutions.

It also has implements a kind of substitution/rewriting: for
"""

from __future__ import annotations

from Expression import *
import enum as _enum

from typing import cast, Optional
from collections.abc import Set, Mapping, MutableMapping


def match(
    dummies: Mapping[str, Variable], pattern: Expression, target: Expression
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
        if isinstance(pattern, Variable) and pattern.name in dummies:
            assert pattern not in target.free_variables(frozenset(dummies.values()))
            # Don't match variables against operators.  There's probably a
            # better way to express this, e.g. by introducing an Operator
            # type.  But for now, this will do.
            if isinstance(target, Node):
                if not (
                    isinstance(target, NumberLiteral) or isinstance(target, Variable)
                ):
                    return None

            # Can we match this variable against this subtree?  Only if the
            # types match.
            assert pattern.type() == dummies[pattern.name].type()
            if pattern.type() == ExpressionType.ANY:
                return {pattern: target}
            target_type = target.type()
            # We need a better way of expressing the type hierarchy.  But for
            # now: a number literal is a math object, a proposition is NOT a
            # math object, and ANY matches anything.
            if (
                target_type == ExpressionType.ANY
                or pattern.type() == target_type
                or (
                    pattern.type() == ExpressionType.OBJECT
                    and target_type == ExpressionType.NUMBER_LITERAL
                )
            ):
                return {pattern: target}
            else:
                return None
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
        for variable, value in subs.items():
            if variable in ret:
                # TODO: Would like to do "equivalent" here, e.g. if +
                # is commutative, consider x + y the same as y + x.
                # This can do == on CompositeExpressions.
                if ret[variable] != value:
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

    return (
        has_head(expr, Implies) or has_head(expr, Equivalent) or has_head(expr, Equal)
    )


def is_instance(
    expr: Expression, rule: Expression, dummies: Mapping[str, Variable] = {}
) -> Optional[Mapping[str, Variable]]:
    """Determines whether 'expr' is an instance of 'rule.'

    returns the substitution that makes them match, or None if there's no match.

    Basically a wrapper on 'match'.  In fact, perhaps 'match' should be
    merged into this.

    NOTE: Doesn't handle ForAll that's under anything other than more ForAlls.
    """

    if has_head(rule, ForAll):
        rule = cast(CompositeExpression, rule)
        return is_instance(expr, rule[1], {**dummies, **rule.get_variables(dummies)})

    return match(dummies, rule, expr)


def try_rule(
    rule: Expression,
    target: Expression,
    direction: Direction,
    dummies: Mapping[str, Variable] = {},
) -> Set[Expression]:
    """Apply "rule" to "target", returns any new expressions it generates.

    If rule is Implies, only applies it to "target"'s root.  If rule is
    Equivalent or Equal, applies it recursively.

    "rule" is always from the context.  If direction == FORWARD,
    then "target" must be from the context, and our results can go in the
    context.  If direction == BACKWARD, then "target" must be from the goals,
    and the result can also go in the goals.

    Returns a possibly empty set() of transformed expressions.

    A "rule" has zero or more foralls at the root, and after stripping
    those off, has either =>, <=> or = at the new root.  If it's =>, we do
    modus ponens at the root of target, i.e. in forward direction, match the
    antecedant against target; when backward, match the consequent.  We do
    this with the pattern matching that comes from the foralls. We treat = and
    <=> as the same.  We should really implement types, so that = only applies
    to math objects, and <=> to propositions, and variables have to have one
    or the other type, but we don't.  try_rule implements
    substitution/rewriting for those.
    """

    # So how to handle "calculation mode"?  First example is 7 - 7.  On the one
    # hand, it would be nice to handle it just like any proof, e.g. we have some
    # starting expression in the context, and we have various rules to transform
    # it.  So basically == is treated just like <==>.
    #
    # On the other hand, we might not know what the answer is, so we won't have
    # a concrete target, such as 0 in the 7 - 7 example.  Instead, we just want
    # to get it as "simple" or "useful" as possible, where the definitions of
    # those may be given, or may be something that the system itself evolves
    # over time.
    #
    # Not having a concrete target can happen when the goal is a theorm too, of
    # course.  "Prove or disprove," or even, "under what conditions is the
    # intermediate value theorem true" or "for which special cases can you prove
    # Goldbach's conjecture" or "here's a comutator and a bunch of QM
    # Hamiltonians, can you produce the stationary states?"  Or "here's the
    # Schrodinger equation, what useful things can you say about it?" and
    # hopefully it can come up with the idea of stationary states itself.
    #
    # And of course we're currently punting on the unknown target case, so maybe
    # we should do that in calc mode too?  i.e. the problem shouldn't be
    # "simplify 7-7" but rather "from the premise 7 - 7, derive the target 0",
    # or the goal "7 - 7 == 0"?

    print(f"rule: {rule}, target: {target}, dummies: {dummies}")

    assert isinstance(rule, CompositeExpression)
    assert is_rule(rule)

    if dummies is None:
        dummies = {}

    if has_head(rule, ForAll):
        # For "forall" we add the variables to dummies and recurse.
        #
        # Wait, how does this interact with having a free variable outside
        # the forall with the same name?  e.g. x == 3 and forall x: x + x == 2*x
        # Could we match the wrong thing in that case?
        return try_rule(
            rule[1],
            target,
            direction,
            {**dummies, **rule.get_variables(dummies)},
        )

    # At this point, if we have exists with a rule under it, we have a funny
    # sort of substitution.  When you have "exists x : f(x) = a" you first
    # need to instantiate x, say with b, then add "f(b) = a" into your
    # assumptions (or non-assumption context?) (as a definition of b),
    # then you're free to use it.
    #
    # In mathematical logic, the witness can't appear in the conclusion.
    # Basically, the witness starts life in an undischarged assumption,
    # and the only thing you can take away when you discharge the assumption
    # is something without the witness.  That seems to be because free
    # variables in formulas are assumed to correspond to specific objects in
    # the domain.  From Wikipedia: "whether a formula such as Phil(x) is true
    # must depend on what x represents. But the sentence ∃x Phil(x) will be
    # either true or false in a given interpretation."
    # https://en.wikipedia.org/wiki/First-order_logic#Free_and_bound_variables
    # So essentially a formula with a free variable is a kind of predicate,
    # where the truth value depends on what the free variable refers to.
    #
    # So I think I want my interpretation of free variables to be a little
    # different.  I think they're understood to come from existential
    # elimination.  That is, we know the existence of them, although perhaps
    # not the uniqueness?  And there's a specific formula that introduces
    # them.  So, for example, we can define b by "7 + b == 0", and that
    # formula is only added to the "definitions" section if we know such a
    # thing exists.
    #
    # I guess what I'm proposing is having a separate "definitions" list,
    # and what logic texts call the final proposition that doesn't have the
    # witness, I'd form by adding an existential quantifier over my
    # definitions and ANDing them to the conclusion?  In other words,
    # when the hypothesis is x + 7 == 11, I might conclude x == 11 + b where
    # 7 + b == 0; the traditional way of stating this is "exists b: 7 + b ==
    # 0 and x == 11 + b."  I'm happy with that, I think.

    # Rename any variables in rule now, so we don't need to worry about them
    # when calling *match_and_substitute below.  Note that, if target is a
    # quantifier, we may also need to rename the variables in it as well,
    # but we don't do that here, in case it turns out to be not needed,
    # and thus we have a "funny" (i.e. generated by renaming) name in the
    # output when we don't need to.

    # "|" means union.
    target_vars = target.bound_variables() | {
        v.name for v in target.free_variables(frozenset())
    }

    quantified = rename_quantified(forall(dummies.values(), rule), target_vars)
    dummies = quantified.get_variables({})
    rule = quantified[1]

    if has_head(rule, Implies):
        # For ==>, if we're working backwards from the conclusion, we see if we
        # can match the RHS, and if so, we return the LHS, with appropriate
        # substitutions and free variables.  If we're working forwards, we match
        # the LHS and substitute on the RHS.
        rule = cast(CompositeExpression, rule)
        if direction == Direction.BACKWARD:
            return match_and_substitute(dummies, rule[2], rule[1], target)
        elif direction == Direction.FORWARD:
            return match_and_substitute(dummies, rule[1], rule[2], target)

    if has_head(rule, Equivalent) or has_head(rule, Equal):
        rule = cast(CompositeExpression, rule)
        # This should be enforced in the rename_quantifier call above.
        assert dummies.keys().isdisjoint(target.bound_variables())
        assert dummies.keys().isdisjoint(
            {v.name for v in target.free_variables(frozenset())}
        )

        # So, we only want to apply this at the top level, i.e.
        # under all the "forall"s, but above everything else.
        result: Set[Expression] = set()
        rhs_is_bound_var = isinstance(rule[2], Variable) and rule[2].name in dummies
        lhs_is_bound_var = isinstance(rule[1], Variable) and rule[1].name in dummies
        if not rhs_is_bound_var:
            result = _recursive_match_and_substitute(dummies, rule[2], rule[1], target)
        if not lhs_is_bound_var:
            result = result | (
                _recursive_match_and_substitute(dummies, rule[1], rule[2], target)
            )

        # Note that, a variable which appears in consequent, but not antecedant,
        # is a new variable were introducing.  If in dummies, it needs to be
        # quantified over.
        result2: Set[Expression] = set()
        for res in result:
            if has_head(res, ForAll):
                res = cast(CompositeExpression, res)
                res_quantified_vars = res[0].get_variables_tree({})
                free_vars = res[1].free_variables(frozenset())
                vars_to_keep = {
                    variable
                    for variable in res_quantified_vars.values()
                    if variable in free_vars
                }
                if len(vars_to_keep) < len(res_quantified_vars):
                    if vars_to_keep:
                        res = forall(vars_to_keep, res[1])
                    else:
                        res = res[1]

            common_vars = {
                variable
                for _, variable in dummies.items()
                if variable in res.free_variables(set())
            }
            if common_vars:
                # Optimization: if the head of 'res' is already ForAll,
                # just add these variables there, rather than creating a new
                # ForAll.
                if has_head(res, ForAll):
                    common_vars.update(res[0].get_variables_tree({}).values())
                    res = res[1]
                res = forall(common_vars, res)
            result2.add(res)
        return result2

    return set()


def match_and_substitute(
    dummies: Mapping[str, Variable],
    antecedent: Expression,
    consequent: Expression,
    target: Expression,
) -> Set[Expression]:
    """Apply 'forall(dummies), antecedent ==> consequent' to target.

    i.e. if "antecedent" matches "target", then return consequent with
    appropriate substitutions.

    If match succeeds, returns a set with one element.  If it fails, returns
    an empty set.

    dummies: the set of variables in antecedent that will take on
    subexpressions of target, which will then be substituted in consequent.
    """

    subs = match(dummies, antecedent, target)
    if subs is not None:
        return {_substitute(subs, consequent)}
    return set()


def _recursive_match_and_substitute(
    dummies: Mapping[str, Variable],
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
    result: Set[Expression] = set()

    subs = match(dummies, antecedent, target)
    if subs is not None:
        result.add(_substitute(subs, consequent))

    if isinstance(target, Node):
        return result

    target = cast(CompositeExpression, target)

    if has_head(target, Quantifier):
        quantified_vars = target.get_variables({})
        # "|" is union
        free_vars = antecedent.free_variables(set()) | consequent.free_variables(set())

        if not free_vars.isdisjoint({v for v in quantified_vars.values()}):
            # This should have happened outside this recursive method.
            assert dummies.keys().isdisjoint(quantified_vars)

            target = rename_quantified(target, {v.name for v in free_vars})
            quantified_vars = target.get_variables({})

            assert free_vars.isdisjoint({v for v in quantified_vars.values()})

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


def _substitute(subs: Mapping[Variable, Expression], expr: Expression) -> Expression:
    """Perform the substitutions given by subs on expr."""

    # What to do about unsubstituted dummies??  I guess just add a
    # ForAll at the front?  e.g. if you want to apply P ^ Q ==> Q backwards,
    # you're introducing a P.
    if isinstance(expr, Node):
        # Kind of ugly that this is special case.  Not sure how to fix that
        # though.
        if isinstance(expr, Quantifier):
            old_vars = expr.get_variables_tree({})
            new_vars = [subs.get(v, v) for v in old_vars.values()]
            # The new names shouldn't be the same as any of the old names ...
            # unless those old names are also being renamed.
            assert len(frozenset(variable.name for variable in new_vars)) == len(
                new_vars
            )
            return expr.__class__(new_vars)

        if isinstance(expr, Variable):
            return subs.get(expr, expr)

        return expr

    expr = cast(CompositeExpression, expr)

    # Actually, this does the wrong thing for quantifiers, since the quantified
    # over variable shadows any instance in what we're trying to substitute.
    # Hmm.
    # Should I just disallow shadowing?
    subed = [_substitute(subs, e) for e in expr]

    head = subed[0]
    if isinstance(head, SumSimplifier):
        total = head.simplify(subed[1:])
        return NumberLiteral(total)

    return CompositeExpression(subed)

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


def new_variable(old_variable: Variable, taken: Set[str]) -> Variable:
    new_name = old_variable.name
    while new_name in taken:
        new_name = "_" + new_name
    return var(new_name, old_variable.type())


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


def rename_quantified(
    quantified: CompositeExpression, taken: Set[str]
) -> CompositeExpression:
    """
    Given a quantified expression, renames any variables that are in "taken".
    """
    assert has_head(quantified, Quantifier)

    ret = _rename_variables(
        frozenset(quantified.get_variables({}).values()), taken, quantified
    )

    return cast(CompositeExpression, ret)


def _rename_variables(
    to_rename: Sequence[Variable], taken: Set[str], expr: Expression
) -> Expression:
    # Note: to_rename is ordered, let's preserve order.
    to_rename = [variable for variable in to_rename if variable.name in taken]
    if not to_rename:
        return expr

    # Need to avoid any names already used in expr.
    # "|" is set union.
    taken = set(
        taken
        | expr.bound_variables()
        | {variable.name for variable in expr.free_variables(frozenset())}
    )

    # Decide on new variable names.
    subs = {}
    for old_var in to_rename:
        new_var = new_variable(old_var, taken)
        taken.add(new_var.name)
        subs[old_var] = new_var

    return _substitute(subs, expr)
