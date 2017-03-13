from Expression import *

# Returns the substitution (as dict) that makes them match, or None if
# there's no match.  Be careful: both the empty dict (meaning there's
# a match that works with any substitution) and None (they don't match
# no matter what you substitute) evaluate as false in Python.


def match(dummies, pattern, target):
    assert isinstance(dummies, set)
    if isinstance(pattern, Node):
        if pattern in dummies:
            return {pattern: target}
        if pattern == target:
            return {}
        return None

    assert isinstance(pattern, CompositeExpression)

    # TODO: Allow something akin to *args, a pattern that matches any
    # number of remaining args.
    if isinstance(target, Node) or len(pattern) != len(target):
        return None

    ret = {}
    for p, t in zip(pattern, target):
        m = match(dummies, p, t)
        if m is None:
            return None
        assert isinstance(m, dict)
        for k, v in m.items():
            if k in ret:
                # TODO: Would like to do "equivalent" here, e.g. if +
                # is commutative, consider x + y the same as y + x.
                # This can do == on CompositeExpressions.
                if ret[k] != v:
                    return None
        ret.update(m)
    return ret


# If a rule matches, transform the target according to the rule and return
# it.  Otherwise, return None.
def try_rule(dummies, rule, target):
    assert isinstance(dummies, set)
    if has_head(rule, ForAll):
        # For "forall" we add the variables to dummies and recurse.
        if isinstance(rule[1], Node):
            assert rule[1] not in dummies
            new_dummies = [rule[1]]
        else:
            assert dummies.isdisjoint(rule[1])
            new_dummies = rule[1]

        return try_rule(dummies.union(new_dummies), rule[2], target)

    if has_head(rule, Implies):
        # For ==> we see if we can match the RHS, and if so, we return the
        # LHS, with appropriate substitutions and free variables.
        return recursive_substitute(dummies, rule[2], rule[1], target)

    if has_head(rule, Equivalent) or has_head(rule, Equal):
        return recursive_substitute(dummies, rule[2], rule[1], target).union(
            recursive_substitute(dummies, rule[1], rule[2], target))

    return set()


def recursive_substitute(dummies, to_match, replacement, target):
    subs = match(dummies, to_match, target)
    if subs is not None:
        return {substitute(subs, replacement)}

    if isinstance(target, Node):
        return set()

    result = set()
    for index, expr in enumerate(target):
        all_changed = recursive_substitute(
            dummies, to_match, replacement, expr)
        for changed in all_changed:
            # newt = target[:index] + (changed,) + target[index+1:]
            newt = list(target)
            newt[index] = changed
            result.add(CompositeExpression(newt))
    return result


def substitute(subs, expr):
    # What to do about unsubstituted dummies??  I guess just add a
    # ForAll at the front?  e.g. if you want to apply P ^ Q ==> Q,
    # you're introducing a P.
    if isinstance(expr, Node):
        return subs.get(expr, expr)

    assert isinstance(expr, CompositeExpression)

    return CompositeExpression([substitute(subs, e) for e in expr])

    # TODO: Handle "or" and "and", e.g. A <==> should be the same as
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
