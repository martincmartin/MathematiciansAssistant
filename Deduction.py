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

    def __repr__(self):  # pragma: no cover
        return repr(id(self)) + ": " + repr(self.node) + \
            " (" + repr(self.depth) + ") -> " + repr(self.parent)


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
