from Expression import *
from pprint import pprint


# Next steps: See "Meta thoughts on the first Dummit problem" in the google doc.
#
# Starting with "P + Q in B," the only rule we can apply is the definition of B,
# so that's easy.  :)  That gives (P + Q) * M == M * (P + Q).
#
# At this point, we can't just use a blind search, since we can always apply
# x == y <==> x + z == y + z for any z, so we have an infinite search space.  We
# can also apply the left and right distributed rules.  And the definition of B,
# the inverse of what we just did, which is pointless.
#
# We have the path_length, which we can use for the distributed rule.
#
# We know (or can add a rule) that there exists P and Q in 2x2 matricies such
# that P * Q != Q * P.  So that suggests that "M" is special, i.e. we need to
# use the premises P in B and Q in B.  Perhaps, for this first problem, we can
# skip that and assume that the premesies are relevant?  Then the question
# becomes, given "(P + Q) * M == M * (P + Q)" and (say) "P in B", how do we find
# a path that "connects" them?

# The question is, how much do I want to bite off for this first question, and
# how much do I leave for later?
#
# 1. I don't want to blindly generate all possible next trees and evaluate them.
# Instead, I want to choose the rule before trying it.  I also want to choose
# which subtree its applied to using heuristics.
#
# 2. I'm happy to have a simple rule that says "always try the premesis first."
# It could even be manual, i.e. I just hard code trying the premises.
#
# 3. We want to be able to work both forward and backward, i.e. from premises to
# conclusions, as well as from conclusions to premesis.

# try_rule() tries to apply the rule at all possible spots and, for == and <==>,
# both the LHS and RHS.  That's not what we want.  Don't want
# recursive_substitute() either.  match() and substitute() can help though.
#
# As for trying the definition of B: maybe that one should always be first?
# Something like "try the information that comes in the problem before more
# general information."  Then that one could reasonably be tried at all
# locations.

##########################
#
# Limitations of the current theorem prover:
#
# - Only checks rules against premises and targets, not other rules.
#
# - Only true inference rules are modus ponens and substitution, although many
#   others could be coded as axioms.  But not ==> introduction and maybe a few
#   others.
#
# - is_instance (used to tell if a proof is complete) only handles ForAll at the
#   root or under other ForAlls at the root, but not under any other operator.
#
# - Breadth first search quickly gets into combinatorial explosion.

def match(dummies, pattern, target):
    """Matches "pattern" against "target"s root, i.e. not recursively.

    "dummies" is the set of Nodes in "pattern" that can match any sub
    expression. (TODO: have types for dummies.)

    Returns the substitution, as dict, that makes them match, or None if there's
    no match.  Be careful: both the empty dict (meaning there's a match that
    works with any substitution) and None (they don't match no matter what you
    substitute) evaluate as false in Python.
    """

    assert isinstance(dummies, set)

    if isinstance(pattern, Node):
        if pattern in dummies:
            assert pattern not in target.free_variables(dummies)
            # This is a hack until we have types: assume any composite
            # expression is boolean valued.
            if isinstance(target, Node) and not target.free_variables(set()):
                return None
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
        for k, v in m.items():
            if k in ret:
                # TODO: Would like to do "equivalent" here, e.g. if +
                # is commutative, consider x + y the same as y + x.
                # This can do == on CompositeExpressions.
                if ret[k] != v:
                    return None
        ret.update(m)
    return ret


def is_rule(expr):
    """Predicate: returns True iff try_rule(expr, target, backwards) could
    return a non-empty set for some target, either forwards or backwards.
    """
    if has_head(expr, ForAll):
        return is_rule(expr[2])

    return has_head(expr, Implies) or \
        has_head(expr, Equivalent) or \
        has_head(expr, Equal)


def try_rule(rule, target, backwards):
    return try_rule_recursive(set(), rule, target, backwards)


def try_rule_recursive(dummies, rule, target, backwards):
    """Try to apply "rule" to "target".  If rule is Implies, only applies it to
    "target"'s root.  If rule is Equivalent or Equal, applies it recursively.
    Returns a possibly empty set() of transformed expressions.
    """
    assert isinstance(dummies, set)
    assert isinstance(backwards, bool)

    if has_head(rule, ForAll):
        # For "forall" we add the variables to dummies and recurse.
        # TODO: rename dummy if its in target.free_variables(dummies) or
        # dummies.
        return try_rule_recursive(
            dummies.union(rule.get_variables(dummies)),
            rule[2],
            target,
            backwards)

    if has_head(rule, Implies):
        # For ==>, if we're working backwards from the conclusion, we see if we
        # can match the RHS, and if so, we return the LHS, with appropriate
        # substitutions and free variables.  If we're working forwards, we match
        # the LHS and substitue on the RHS.
        if backwards:
            return match_and_substitute(dummies, rule[2], rule[1], target)
        else:
            return match_and_substitute(dummies, rule[1], rule[2], target)

    if has_head(rule, Equivalent) or has_head(rule, Equal):
        return recursive_match_and_substitute(
            dummies, rule[2], rule[1], target).union(
            recursive_match_and_substitute(
                dummies, rule[1], rule[2], target))

    return set()


def match_and_substitute(dummies, to_match, replacement, target):
    """Tries to match the rule "to_match" to the root of "target".

    Returns a (possibly empty) set().

    dummies: the set of variables in replacement that will be set to things in
    to_match."""
    assert isinstance(dummies, set)

    subs = match(dummies, to_match, target)
    if subs is not None:
        return {substitute(subs, replacement)}
    return set()


def recursive_match_and_substitute(dummies, to_match, replacement, target):
    """Tries to match the rule "to_match" to all subexpressions of "target".

    Returns a (possibly empty) set().

    dummies: the set of variables in replacement that will be set to things in
    to_match."""
    assert isinstance(dummies, set)

    result = set()

    subs = match(dummies, to_match, target)
    if subs is not None:
        result.add(substitute(subs, replacement))

    if isinstance(target, Node):
        return result

    for index, expr in enumerate(target):
        all_changed = recursive_match_and_substitute(
            dummies, to_match, replacement, expr)
        for changed in all_changed:
            # new_target = target[:index] + (changed,) + target[index+1:]
            new_target = list(target)
            new_target[index] = changed
            result.add(CompositeExpression(new_target))
    return result


def is_instance(rule, target, dummies=set()):
    """Determines whether 'target' is an instance of 'rule.'

    returns the substitution that makes them match, or None if there's no match.

    NOTE: Doesn't handle ForAll that's under anything other than more ForAlls.
    """

    if has_head(rule, ForAll):
        return is_instance(
            rule[2], target, dummies.union(
                rule.get_variables(dummies)))
    else:
        return match(dummies, rule, target)


def substitute(subs, expr):
    """Given an expression, and a hash from vars to subexpressions, substitute the
    subexspressions into the vars."""
    assert isinstance(subs, dict)
    # What to do about unsubstituted dummies??  I guess just add a
    # ForAll at the front?  e.g. if you want to apply P ^ Q ==> Q backwards,
    # you're introducing a P.
    if isinstance(expr, Node):
        return subs.get(expr, expr)

    assert isinstance(expr, CompositeExpression)

    return CompositeExpression([substitute(subs, e) for e in expr])

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


# For the heuristic of the path length between two nodes: Need to find
# the common ancestor, then the length can be computed from the level
# (depth) of the two nodes and ancestor.  To find the common ancestor,
# we can compute "parent" links and depth, then just follow parent
# links at the same level until we find ones that are equal.
#
# Or, we could have a hash from id -> (level, expr).  As we do a
# depth-first search, we keep track of the path to the root
# (equivalent to the parent pointers).  When we find a target leaf, we
# can query all parents to find the first one (searching backwards)
# that is on the path to the other kind of target.  That means, when
# we find one kind of target (either P or M), we also need to anotate
# its path to the root to say you can get to P or M from here.  We
# might even need the list of Ps or Ms you can get to.  Hmm.

# Python doesn't have a singly linked list class, so we roll our own.
# Wonder if a named tuple would be better: hashable, constant.
class PathToRoot:
    def __init__(self, node, parent):
        self.node = node
        self.parent = parent
        self.depth = parent.depth + 1 if parent else 0


# Returns the number of edgues between node1 and node2.  For example, in
# M * (P + Q), there are 3 edges between M and P: M -> *, * -> + and + -> P.
def path_length(node1, node2, expr):
    assert node1 != node2  # TODO: Handle when the nodes are the same.
    assert isinstance(expr, Expression)
    # Only leaves for now.
    assert isinstance(node1, Node)
    assert isinstance(node2, Node)

    # This algorith is N * M, where N is the number of node1, and M the number
    # of node2.  But there should be more efficient algorithms, since many
    # leaves for the same target will have a common ancestor at some point.

    # First, get all paths from root to the targets.
    target1_paths = []
    path_length_helper(node1, expr, None, target1_paths)

    target2_paths = []
    path_length_helper(node2, expr, None, target2_paths)

    # Next, for each pair of targets, find the common ancestor and calculate the
    # depth.
    ret = []
    for path1 in target1_paths:
        for path2 in target2_paths:
            thing1 = path1.parent
            thing2 = path2.parent

            # Whichever one is at a higher depth, iterate until the depths
            # match.
            while thing1.depth > thing2.depth:
                thing1 = thing1.parent
            while thing2.depth > thing1.depth:
                thing2 = thing2.parent

            # Now iterate until we find the common ancestor.
            while id(thing1.node) != id(thing2.node):
                thing1 = thing1.parent
                thing2 = thing2.parent

            assert thing1.depth == thing2.depth

            path_len = (path1.depth - thing1.depth) + \
                (path2.depth - thing1.depth)
            ret.append((path_len, path1.node, path2.node))
    # Sort by path_len.
    ret.sort(key=lambda x: x[0])
    return ret


# Appends to paths_from_targest_to_root, the paths from exp to all nodes which
# == target, with parent_path_to_root pre-pended.
def path_length_helper(
        target,
        expr,
        parent_path_to_root,
        paths_from_targets_to_root):
    if expr == target:
        paths_from_targets_to_root.append(
            PathToRoot(expr, parent_path_to_root))
    elif isinstance(expr, CompositeExpression):
        path_to_root = PathToRoot(expr, parent_path_to_root)
        for subtree in expr:
            path_length_helper(
                target,
                subtree,
                path_to_root,
                paths_from_targets_to_root)


class RulePosition:
    def __init__(self, rule):
        self.premise = 0
        self.target = 0
        self.rule = rule


def try_rules(premises, target, rules):
    """This is where the heuristics come in.  We're trying to find a path from
    "rules" + "premises" to "target".
    """
    # For now, we don't use any heuristics, just a search forward from premises
    # and backwards from target.  When this proves too slow, we can switch to
    # something smarter.

    # There's a deduction rule (==> introduction) where we add an arbitrary
    # expression to the premises, derive some conclusion, then we can add
    # 'new_premise ==> conclusion' to the original set of premises.  But for
    # now, we'll skip that rule.

    premises_list = list(premises)
    premises_and_rules_set = set(premises_list + rules)

    targets_list = [target]
    targets_set = set(targets_list)

    # The rules are really premises, or at least, ones with a root connective
    # ==>, <==> or ==, possibly under any number of ForAlls.  And we'll want to
    # add any such derived premises to the 'rules' list.  Hmm.

    rules = [RulePosition(rule) for rule in rules]

    # We want to keep the expressions in a list, and for each rule, apply it in
    # order from index 0 on up.  Then for each rule, we simply need to keep the
    # highest index that we've applied the rule to.  We still need a hash set to
    # unique them.

    # For now, we don't try to apply rules to other rules, just to premises and
    # targets.  Although it would be easy...

    for iter in range(1000):
        made_new_expr = False
        rule_index = 0
        print('+++++++++++++++  Pass ' + str(iter))
        while rule_index < len(rules):
            rule_pos = rules[rule_index]
            assert rule_pos.premise <= len(premises_list)
            assert rule_pos.target <= len(targets_list)

            print('********** Rule: ' + str(rule_pos.rule))

            if rule_pos.premise < len(premises_list):
                exprs = try_rule(
                    rule_pos.rule, premises_list[rule_pos.premise], True)

                print(
                    str(premises_list[rule_pos.premise]) + ' -> ' + repr(exprs))

                for move in exprs:
                    if move not in premises_and_rules_set:
                        # Are we there yet?
                        if move in targets_set:
                            print(move)
                            print("DONE!!")
                            return True

                        # We have a new premise / rule!
                        for target in targets_list:
                            subs = is_instance(move, target)
                            if subs is not None:
                                print(str(target) +
                                      ' is an instance of ' +
                                      str(move) + ' subs ' +
                                      str(subs) + '  !!!!!!')

                                return True

                        made_new_expr = True

                        if is_rule(move):
                            # Could this end up beina depth first search, if
                            # each rule creates a new rule?  Hmm.  If so, could
                            # replace the 'while' above with only looping up to
                            # the size of rules at the start.
                            rules.append(RulePosition(move))
                            print('rules:  ' + str(move))
                        else:
                            premises_list.append(move)
                            print('premises:  ' + str(move))

                        premises_and_rules_set.add(move)

                rule_pos.premise += 1

            if rule_pos.target < len(targets_list):
                exprs = try_rule(
                    rule_pos.rule, targets_list[rule_pos.target], False)

                print(
                    str(targets_list[rule_pos.target]) + ' -> ' + repr(exprs))

                for move in exprs:
                    if move not in targets_set:
                        if move in premises_and_rules_set:
                            print(move)
                            print("DONE!!")
                            return True

                        for rule_p in rules:
                            subs = is_instance(rule_p.rule, move)
                            if subs is not None:
                                print(str(move) +
                                      ' is an instance of ' +
                                      str(rule_p.rule) + ' subs ' +
                                      str(subs) + '  !!!!!!')
                                return True

                        made_new_expr = True
                        targets_list.append(move)
                        targets_set.add(move)
                        print('targets:  ' + str(move))

                rule_pos.target += 1

            rule_index += 1

        if not made_new_expr:
            return False

    return False
