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
    dummies: Mapping[Variable, ExpressionType], pattern: Expression,
        target: Expression
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
            assert pattern not in target.free_variables(dummies.keys())
            # Can we match this variable against this subtree?  Only if the
            # types match.
            pattern_type = dummies[pattern]
            if pattern_type == ExpressionType.ANY:
                return {pattern: target}
            target_type = target.type()
            # We need a better way of expressing the type hierarchy.  But for
            # now: a number literal is a math object, a proposition is NOT a
            # math object, and ANY matches anything.
            if target_type == ExpressionType.ANY or \
                    pattern_type == target_type or \
                    (pattern_type == ExpressionType.OBJECT and
                     target_type == ExpressionType.NUMBER_LITERAL):
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

    return has_head(expr, Implies) or has_head(expr, Equivalent) or has_head(
        expr, Equal
    )


def is_instance(
    expr: Expression, rule: Expression,
    dummies: Mapping[Variable, ExpressionType] = {}
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
            expr, rule[1], {**dummies, **rule.get_variables(dummies)}
        )

    return match(dummies, rule, expr)


def try_rule(
        rule: Expression, target: Expression, direction: Direction,
        dummies: Mapping[Variable, ExpressionType] = {}) \
        -> Set[Expression]:
    """Apply "rule" to "target", returns any new expressions it generates.

    If rule is Implies, only applies it to "target"'s root.  If rule is
    Equivalent or Equal, applies it recursively.

    "rule" is always from the context.  If direction == FORWARD,
    then "target" must be from the context, and our results can go in the
    context.  If direction == BACKWARD, then "target" must be from the goals,
    and the result can also go in the goals.

    Returns a possibly empty set() of transformed expressions.

    A "rule" has zero or more foralls at the root, and after stripping
    those off, has either =>, <=> or = at the new root.  If it's =>, we do modus
    ponens at the root of target, i.e. in forward direction, match the
    antecedant against target; when backward, match the consequent.  We do
    this with the pattern matching that comes from the foralls. We treat = and
    <=> as the same.  We should really implement types, so that = only applies
    to math objects, and <=> to propositions, and variables have to have one
    or the other type, but we don't.  try_rule implements
    substitution/rewriting for those.
    """

    # So given x + 7 = 11, we want the system to think "hey if I could turn
    # the 7 into a zero that would be gucci."
    # Then one idea is, if we have foo = bar, we can conclude f(foo) = f(
    # bar).  And for these problems, where the user knows we have a single
    # solution, that will be good enough.  So essentially we want to add "7 +
    # b = 0" to the ... assumptions?  context?  Then we can do (x + 7) + b ==
    # 11.  How is "foo = bar -> foo + b = bar + b" encoded in the system?
    # One way is to have forall x, x = x, then instantiate that for, say,
    # 11 + b = 11 + b, then we change the left 11 into x + 7.  Seems torturous.
    # We'd like to directly express "if foo = bar, then f(foo) = f(bar)."
    # Does this mean giving the system a notion of a function??  Even an
    # axiom schema for expr = expr, which we could instantiate with expr = f(
    # foo), seems indirect.  Special casing it for + and * is lame.  But if
    # we have an explicit rule for all f(), that requires quantifying over f(
    # ), which seems second order.
    #
    # How did ancient peoples come up with this idea?  Or even not so ancient
    # peoples?  I think the idea of "subtract 7 from both sides" is different
    # the intuitive (at least to me) notion that from x + 7 = 11, we conclude
    # x = 11 - 7.  In the second one, you're moving the 7 to the other side,
    # and it changes sign.  That's how I thought if it when I was younger and
    # algebra as an opaque set of rules.  Now I think of the "subtract from
    # both sides" thing.
    #
    # The ancient Greeks didn't represent algebra this way.  Instead,
    # they were word problems involving lines, i.e. a number was thought of
    # as the length of a line segment.  So x + 7 = 11 is something like "a
    # line, when a second line of length 7 is placed end to end with it,
    # total length is 11 units.  How long is the original line?"
    #
    # The concept of function didn't come until Leibniz in 1692.  Before
    # that, it was implicit in trigonometric and logarithmic tables.
    #
    # For now, maybe we just give the rules "forall a, b, c: a = b => a + c =
    # b + c" and for multiplication?  It can be derived from substitution,
    # but maybe we skip that for now.  Because we're already starting from a
    # heavily symbolized description.
    #
    # In teaching the algebra, you can talk about adding something to one
    # side, then adding it to the other side to keep it balanced.  Similar
    # for subtracting I would think.
    #
    # How does this generalize to square and square root? It's enough to let
    # you complete the square, e.g. put it in the form a(x + b)^2 + c = 0,
    # then get (x + b)^2 by itself.  Then what?  You get into +/- stuff,
    # e.g. x^2 = c => x = +/- c.  In a sense, it benefits from new notation (
    # the +/- symbol) to save you doing the same operations to both
    # solutions.  So, I think I'm happy with rules for + and *, and leaving
    # things like sqrt() until later.
    #
    # This really is subtly different than "given assumption, derive
    # conclusion."  It's not just "one thing we know about x is x^2 = 4,
    # " it's "EVERYTHING we know about x is x^2 = 4."  I guess this is where
    # sets come in?  i.e. we define a set S = {x | x*x = 4}, and can ask what
    # are the elements of S, i.e. what is S?  Anyway, can have just the + and
    # * rules for now to unblock me.  Still feels unsatisfying though.
    #
    # In fact, solving a cubic is non-trivial.  A standard way taught to
    # students is to find one real root r -- every cubic with real coefficients
    # has at least one real root -- then do synthetic division by (x - r) to
    # get a quadratic.
    #
    # So, we have some manipulation rules that are given to the system,
    # in addition to the ordered field axioms.  So the system (a) can solve
    # problems involving x, + and zeros, and (b) we have x, + and 7,
    # so we need some way to get rid of the 7.  So we look at our axioms, and

    # Free variables are considered "constants" in the sense that they name a
    # single number, and have whatever properties are given by the premises.
    # So, for example, from exists(b, b + 5 = 0), we can conclude c + 5 = 0,
    # as long as c doesn't appear free in any premise.  Essentially this
    # defines everything we know about c.  e.g. we could have d * d = 4,
    # and we wouldn't be able to determine whether d is 2 or -2.  We just
    # know there is a d with that property.  In fact, that's the only thing
    # you can do with exists at the root of a premise, is to introduce a
    # witness.
    #
    # This fact that the witness can't exist free in *any* premise is a pain in
    # the ass, although we could get around it with a gensym.  Worse is when
    # introducing a forall (when working forward); you do that when you've
    # proven a statement with
    # a witness that doesn't appear in any of the other premises.  In that
    # case, gensym doesn't save you, and you need to check that it doesn't
    # appear in (a minimal subset of?) the premises.  Note that working
    # backwards it does save you: given a goal of "forall x: P", you can
    # gensym "x" and change the goal to P(newx / x).  This is what Coq's
    # "intros" does.  By symmetry, we should have the same problem with
    # exists when working backwards: going from a goal with a specific value,
    # e.g. "n * n = n", and changing it to a goal with an exists,
    # e.g. "exists n : n * n = n".  As far as I know, Coq only goes the
    # "gensym" direction, although it allows you to specify the name of the
    # generic witness, so has to keep track of the set of free variables
    # anyway.
    #
    # I think we need to keep our set of "root premises" separate from all
    # the statements we derive from them, essentially everything to the left
    # of the turnstile, so we can check whether or not a variable is among
    # them.
    #
    # How do Coq and Lean handle this?  For Coq, if the context has "exists
    # x: P", then we can destruct it to obtain a witness x, along with P in the
    # context.  For forall generalization, "intros."  Can we only forall
    # introduction in the goal, and exists elimination in the premise?  Coq
    # does have the "generalize dependent" tactic, which does the opposite of
    # intros: if the goal has some statement about n, it turns it into
    # "forall n: statement about n."
    #
    # Anyway, we have a choice: do we introduce a finite set of inference
    # rules?  Or have rules as axioms with a simple machinery?  The argument
    # for simple machinery is that the key behavior we need is pattern
    # matching and substitution, involving metavariables.  For example,
    # the rule for removing a conjunction is, if we know P & Q, then we can
    # conclude P.  But that can also be written "forall {P, Q}, P & Q => P."
    # However, others may not be naturally expressed that way.  For example,
    # there's proof by contradiction: not P => Q and not P => not Q,
    # then conclude P.  Or if P => Q and not P => Q, then conclude Q.  What's
    # a natural way to encode those?
    #
    # So for e.g. proof by contradiction, we want to start a new sub-frame
    # with the extra assumption ~P, then derive Q & ~Q, and finally add P to
    # the context.  Similarly, we'll want to start a sub-frame with extra
    # assumption P and prove Q; then a parallel sub-frame with ~P and prove
    # Q; then we can add Q to the context without adding either P or ~P.
    #
    # So you could get this with a general "add sub frame" action which lets
    # you derive P => Q in the outer frame.  Then have a rule that from "P =>
    # Q & ~Q" you derive ~P, and from P => Q and ~P => Q you derive Q.
    #
    # So, do I want to have metavariables, or just encode rules?  Or maybe
    # punt on all this until I need it, and only implement exists-elimination
    # now?
    #
    # So how does exists-elimination work with matching?  The exists statement
    assert is_rule(rule)
    rule = cast(CompositeExpression, rule)

    if dummies is None:
        dummies = frozenset()

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
    target_vars = target.bound_variables() | target.free_variables(frozenset())
    quantified = rename_quantified(forall(dummies, rule), target_vars)
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
        assert dummies.keys().isdisjoint(target.free_variables(frozenset()))
        # bound_in_target = target.bound_variables()
        # if not dummies.isdisjoint(bound_in_target):
        #     temp = rename_quant(forall(dummies, rule),
        #                         bound_in_target)
        #     dummies = temp.get_variables(frozenset())
        #     rule = temp[1]

        # So, we only want to apply this at the top level, i.e.
        # under all the "forall"s, but above everything else.
        result = set()
        rhs_is_bound_var = isinstance(rule[2], Variable) and rule[2] in dummies
        lhs_is_bound_var = isinstance(rule[1], Variable) and rule[1] in dummies
        if not rhs_is_bound_var:
            result = _recursive_match_and_substitute(dummies, rule[2], rule[1],
                                                     target)
        if not lhs_is_bound_var:
            result = result.union(
                _recursive_match_and_substitute(dummies, rule[1], rule[2],
                                                target))

        # Note that, a variable which appears in consequent, but not antecedant,
        # is a new variable were introducing.  If in dummies, it needs to be
        # quantified over.
        result2 = set()
        for res in result:
            if has_head(res, ForAll):
                res = cast(CompositeExpression, res)
                res_quantified_vars = res[0].get_variables_tree({})
                vars_to_keep = {variable: typ for variable, typ in
                                res_quantified_vars.items() if variable in
                                res[1].free_variables(set())}
                if len(vars_to_keep) < len(res_quantified_vars):
                    if vars_to_keep:
                        res = forall(vars_to_keep, res[1])
                    else:
                        res = res[1]

            common_vars = {variable: typ for variable, typ in dummies.items()
                           if variable in res.free_variables(set())}
            if common_vars:
                # Optimization: if the head of 'res' is already ForAll,
                # just add these variables there, rather than creating a new
                # ForAll.
                if has_head(res, ForAll):
                    common_vars.update(res[0].get_variables_tree({}))
                    res = res[1]
                res = forall(common_vars, res)
            result2.add(res)
        return result2

    return set()


def match_and_substitute(
    dummies: Mapping[Variable, ExpressionType],
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
    dummies: Mapping[Variable, ExpressionType],
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
        quantified_vars = target.get_variables({})
        # "|" is union
        free_vars = antecedent.free_variables(set()) | \
            consequent.free_variables(set())

        if not free_vars.isdisjoint(quantified_vars.keys()):
            # This should have happened outside this recursive method.
            assert dummies.keys().isdisjoint(quantified_vars)

            target = rename_quantified(target, free_vars)
            quantified_vars = target.get_variables({})

            assert free_vars.isdisjoint(quantified_vars.keys())

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
            old_vars = expr.get_variables_tree({})
            new_vars = [(subs.get(v, v), t) for v, t in old_vars.items()]
            # The new names shouldn't be the same as any of the old names ...
            # unless those old names are also being renamed.
            assert len(frozenset(variable for variable, typ in new_vars)) == \
                   len(new_vars)
            return expr.__class__(new_vars)

        if isinstance(expr, Variable):
            return subs.get(expr, expr)

        return expr

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


def rename_quantified(
    quantified: CompositeExpression, taken: Set[Variable]
) -> CompositeExpression:
    """
    Given a quantified expression, renames any variables that are in "taken".
    """
    assert has_head(quantified, Quantifier)

    ret = _rename_variables(quantified.get_variables({}).keys(),
                            taken,
                            quantified)

    return cast(CompositeExpression, ret)


def _rename_variables(to_rename: Set[Variable], taken: Set[Variable],
                      expr: Expression) -> Expression:
    # Note: to_rename is ordered, let's preserve order.
    to_rename = [variable for variable in to_rename if variable in taken]
    if not to_rename:
        return expr

    # Need to avoid any names already used in expr.
    # "|" is set union.
    taken = set(taken | expr.bound_variables() | expr.free_variables(
        frozenset()))

    # Decide on new variable names.
    subs = {}
    for old_name in to_rename:
        new_name = new_variable(old_name, taken)
        taken.add(new_name)
        subs[old_name] = new_name

    return _substitute(subs, expr)
