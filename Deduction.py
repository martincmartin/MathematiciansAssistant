from Expression import *
# from pprint import pprint
from typing import *
# from abc import ABCMeta, abstractmethod
from enum import Enum, auto


# So we proved the first two problems, but using brute force.  Would like to
# capture a more human method instead.  For example, we would like to work
# primarily forward, from the start to the goal, rather than backward from the
# goal.
#
# We want to prove "P in B and Q in B -> P + Q in B."
#
# Some tactics to start:
#
# 1. We can apply any "obvious" techniques to the context, independent of the
#    goal, such as simplification (e.g. collapsing constants) or, in our case,
#    applying the definition.
#
# 2. We can work backwards from the goal, without thinking explicitly about the
#    premises / context, in the same way as 1., i.e. apply simplifications and
#    definitions.
#
# 3. Note similarities & differences between the context and the goal, and see
#    what might transform the start into the goal.
#
# Ideally, we would learn how much of the goal, context, etc. to look at for
# each tactic.  But we can add that later.

# So what do we need?
#
# - Explicit context.
# - Explicit goal(s).
#


# Next steps: See "Meta thoughts on the first Dummit problem" in the google doc.
#
# Starting with "P + Q in B," the only rule we can apply is the definition of B,
# so that's easy.  :) That gives (P + Q) * M == M * (P + Q).  [That's not
# technically true, you can also apply rules that add random crap.  But it's the
# only rule that 'makes sense.']
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

# As for trying the definition of B: maybe that one should always be first?
# Something like "try the information that comes in the problem before more
# general information."  Then that one could reasonably be tried at all
# locations.

##########################
#
# Limitations of the current theorem prover:
#
# - Only checks rules against premises and goals, not other rules.
#
# - Only true inference rules are modus ponens and substitution, although many
#   others could be coded as axioms.  But not ==> introduction and maybe a few
#   others.
#
# - is_instance (used to tell if a proof is complete) only handles ForAll at the
#   root or under other ForAlls at the root, but not under any other operator.
#
# - Breadth first search quickly gets into combinatorial explosion.
#
# - Assumes rules only apply to single expression, so can't do "and
#   introduction" for example.
# TODO: Maybe separate out the "general_rules", since we'll need the concept of
# sub-goals and provisional context for proving implications anyway?


# Wish I could make this a NamedTuple, but recursively typed NamedTuples and
# mypy are currently broken, see https://github.com/python/mypy/issues/3836
# class ExprAndParent(NamedTuple):
#    expr: Expression
#    parent: 'ExprAndParent'

class ExprAndParent:
    _expr: Expression
    _parent: 'ExprAndParent'

    def __init__(self, expr: Expression,
                 parent: Optional['ExprAndParent']) -> None:
        self._expr = expr
        self._parent = parent

    @property
    def expr(self) -> Expression:
        return self._expr

    @property
    def parent(self) -> 'ExprAndParent':
        return self._parent


class RulePosition:
    rule: ExprAndParent
    premise: int = 0
    target: int = 0

    def __init__(self,
                 rule: Union[ExprAndParent, Expression],
                 parent=None) -> None:
        if isinstance(rule, ExprAndParent):
            assert parent is None
            self.rule = rule
        else:
            assert isinstance(rule, Expression)
            self.rule = ExprAndParent(rule, parent)

    def __repr__(self):
        return '[premise: ' + str(self.premise) + ', target: ' + \
               str(self.target) + ', rule: ' + str(self.rule.expr) + ']'


class Direction(Enum):
    FORWARD = auto()
    BACKWARD = auto()
    BOTH = auto()


class GoalExprsABC(Mapping[Expression, ExprAndParent]):
    # noinspection PyUnusedLocal
    @abstractmethod
    def __init__(self, goals: Sequence[Expression]) -> None:
        pass

    @abstractmethod
    def all_exprs(self) -> Sequence[ExprAndParent]:
        return []

    @abstractmethod
    def add(self, move_and_parent: ExprAndParent) -> None:
        raise KeyError

    def __repr__(self):
        return '\n'.join(str(expr) for expr in self)


class GoalExprsBruteForce(GoalExprsABC):
    _exprs_list: MutableSequence[ExprAndParent]
    _exprs_map: MutableMapping[Expression, ExprAndParent]

    def __init__(self, exprs: Sequence[Expression]) -> None:
        super().__init__(exprs)
        assert all(isinstance(e, Expression) for e in exprs)
        self._exprs_list = [ExprAndParent(e, None) for e in exprs]
        self._exprs_map = {
            expr_and_parent.expr: expr_and_parent for expr_and_parent in
            self._exprs_list}

    def __len__(self) -> int:
        return len(self._exprs_list)

    def __getitem__(self, key: Expression) -> ExprAndParent:
        return self._exprs_map[key]

    def __iter__(self) -> Iterator[Expression]:
        return self._exprs_map.__iter__()

    def all_exprs(self) -> Sequence[ExprAndParent]:
        return self._exprs_list

    def add(self, expr_and_parent: ExprAndParent) -> None:
        self._exprs_list.append(expr_and_parent)
        self._exprs_map[expr_and_parent.expr] = expr_and_parent


class Exprs(GoalExprsABC):
    exprs_non_rules: List[ExprAndParent]
    exprs_rules: List[RulePosition]
    parent: Optional['Exprs']
    exprs_map: Dict[Expression, ExprAndParent]

    def __init__(self, exprs: List[Expression],
                 parent: Optional['Exprs'] = None) -> None:
        super().__init__(exprs)
        self.parent = parent

        assert all(isinstance(e, Expression) for e in exprs)
        self.exprs_non_rules = [ExprAndParent(e, None)
                                for e in exprs if not is_rule(e)]
        self.exprs_rules = [RulePosition(e, None)
                            for e in exprs if is_rule(e)]

        self.exprs_map = {expr.expr: expr for expr in
                          self.exprs_non_rules +
                          [r.rule for r in self.exprs_rules]}

    def add(self, expr_and_parent: ExprAndParent):
        if is_rule(expr_and_parent.expr):
            self.exprs_rules.append(RulePosition(expr_and_parent))
        else:
            self.exprs_non_rules.append(expr_and_parent)
        self.exprs_map[expr_and_parent.expr] = expr_and_parent

    def __contains__(self, expr: Expression) -> bool:
        return expr in self.exprs_map or (self.parent and (expr in self.parent))

    def __getitem__(self, key: Expression) -> ExprAndParent:
        if key in self.exprs_map:
            return self.exprs_map[key]
        return self.parent[key]

    # Used to iterate over all expressions, to see if a newly generated
    # expression is an instance of any of them, meaning the proof is done.
    def __iter__(self) -> Iterator[Expression]:
        return [expr.expr for expr in self.all_exprs()].__iter__()

    def __len__(self) -> int:
        return len(self.exprs_map) + (len(self.parent) if self.parent else 0)

    def immediate_non_rules(self) -> List[ExprAndParent]:
        return self.exprs_non_rules

    def all_non_rules(self) -> List[ExprAndParent]:
        if self.parent:
            return self.exprs_non_rules + self.parent.all_non_rules()
        else:
            return self.exprs_non_rules

    def immediate_rules(self) -> List[ExprAndParent]:
        return [r.rule for r in self.exprs_rules]

    def all_rules(self) -> List[RulePosition]:
        if self.parent:
            return self.parent.all_rules() + self.exprs_rules
        else:
            return self.exprs_rules

    def equalities(self) -> Sequence[ExprAndParent]:
        parent_equalities = self.parent.equalities() if self.parent else []
        return [
            rule_pos.rule for rule_pos
            in self.exprs_rules
            if is_equality(rule_pos.rule.expr)] + parent_equalities

    def all_exprs(self) -> List[ExprAndParent]:
        # This won't work in general, because when we add a rule, it will change
        # the index of all elements of exprs_list.  Oi.
        return self.exprs_non_rules + self.immediate_rules() + \
               (self.parent.all_exprs() if self.parent else [])

    def __str__(self) -> str:
        if self.parent:
            return str(self.exprs_map.values()) + str(self.parent)
        return str(self.exprs_map.values())


# TODO: Type checking of ExprsClass using an abstract base class.


class ProofState:
    goals: GoalExprsABC
    verbose: bool
    context: Exprs

    def __init__(self,
                 context: List[Expression],
                 goal: Expression,
                 general_rules: List[Expression],
                 goal_exprs_class: Type[GoalExprsABC],
                 verbose: bool) -> None:
        self.verbose = verbose

        general = Exprs(general_rules)
        self.context = Exprs(context, general)

        self.goals = goal_exprs_class([goal])

    def is_instance(self, expr: Expression, rule: Expression):
        subs = is_instance(expr, rule)
        if self.verbose and subs is not None:
            print(str(expr) + ' is an instance of ' +
                  str(rule) + ' subs ' + str(subs) + '  !!!!!!')
        return subs

    def try_rule(
            self,
            rule: Expression,
            expr_and_parent_in: ExprAndParent,
            already_seen: GoalExprsABC,
            targets: Mapping[Expression, ExprAndParent],
            direction: Direction) -> \
            Union[bool, Tuple[ExprAndParent, ExprAndParent]]:
        """If it finds a solution, returns a tuple of the path within
        already_seen, and the path within targets.  If it doesn't find a
        solution, returns a bool as to whether or not it at least generated a
        new expression which it added to already_seen.
        """
        assert all(isinstance(t, Expression) for t in targets)
        assert isinstance(rule, CompositeExpression)
        assert isinstance(expr_and_parent_in, ExprAndParent)

        exprs = try_rule(rule, expr_and_parent_in.expr, direction)
        assert all(isinstance(e, Expression) for e in exprs)

        if self.verbose:
            print(
                'try_rule: ' +
                str(expr_and_parent_in.expr) +
                ' was transformed into ' +
                repr(exprs))

        added = False
        for move in exprs:
            if move in already_seen:
                continue

            move_and_parent = ExprAndParent(move, expr_and_parent_in)

            # Ideally, in the case of P in B -> P * M == M * P, we'd
            # recognize that the latter is equivalent to the former, and is
            # strictly more useful so we can get rid of the former.  But I
            # think that takes some global knowledge of the proof, e.g. that
            # "P in B" doesn't appear in the goal in any form, or in any
            # other premises, etc.  So we'll skip that for now.

            found = self.match_against_exprs(move, targets)
            if found:
                assert isinstance(found, ExprAndParent)
                return found, move_and_parent
            already_seen.add(move_and_parent)
            added = True

        return added

    def match_against_exprs(
            self,
            move: Expression,
            targets: Mapping[Expression, ExprAndParent]) -> ExprAndParent:
        """Determines whether move equals or is_instance any
        element of targets.

        If so, returns the element.  If not, returns None.
        """
        if move in targets:
            return targets[move]
        assert all(isinstance(t, Expression) for t in targets)

        return next((targets[target] for target in targets if
                     self.is_instance(move, target) is not None),
                    None)


def match(dummies: AbstractSet[Node], pattern: Expression,
          target: Expression) -> \
        Optional[Mapping[Expression, Expression]]:
    """Matches "pattern" against "target"s root, i.e. not recursively.

    "dummies" is the set of Nodes in "pattern" that can match any sub
    expression. (TODO: have types for dummies.)

    Returns the substitution, as dict, that makes them match, or None if there's
    no match.  Be careful: both the empty dict (meaning there's a match that
    works with any substitution) and None (they don't match no matter what you
    substitute) evaluate as false in Python.
    """

    assert isinstance(dummies, set)
    assert isinstance(pattern, Expression)
    assert isinstance(target, Expression)

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

    pattern = cast(CompositeExpression, pattern)

    # TODO: Allow something akin to *args, a pattern that matches any
    # number of remaining args.
    if isinstance(target, Node):
        return None
    target = cast(CompositeExpression, target)

    if len(pattern) != len(target):
        return None

    ret: MutableMapping[Expression, Expression] = {}
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


def is_equality(expr: Expression) -> bool:
    """Predicate. returns True iff expr is a (possibly universally quantified)
    equality.
    """
    if has_head(expr, ForAll):
        return is_equality(cast(CompositeExpression, expr)[2])

    return has_head(expr, Equal)


def get_lhs(expr: Expression) -> Expression:
    assert is_equality(expr)
    while has_head(expr, ForAll):
        expr = cast(CompositeExpression, expr)
        # Need to do something with the variables here.  Hmm.  Maybe this is why
        # logic traditionally has the concept of free vs bound variables?
        expr = expr[2]
    assert has_head(expr, Equal)
    expr = cast(CompositeExpression, expr)
    return expr[1]


def is_rule(expr: Expression) -> bool:
    """Predicate. returns True iff try_rule(expr, target, backwards) could
    return a non-empty set for some target, either forwards or backwards.
    """
    if has_head(expr, ForAll):
        return is_rule(cast(CompositeExpression, expr)[2])

    return has_head(expr, Implies) or \
        has_head(expr, Equivalent) or \
        has_head(expr, Equal)


def try_rule(rule: Expression, target: Expression, direction: Direction):
    return try_rule_recursive(set(), rule, target, direction)


def try_rule_recursive(
        dummies,
        rule: Expression,
        target: Expression,
        direction: Direction) -> AbstractSet[Expression]:
    """Try to apply "rule" to "target".  If rule is Implies, only applies it to
    "target"'s root.  If rule is Equivalent or Equal, applies it recursively.
    Returns a possibly empty set() of transformed expressions.
    """
    assert isinstance(dummies, set)
    assert isinstance(direction, Direction)
    assert is_rule(rule)
    rule = cast(CompositeExpression, rule)

    if has_head(rule, ForAll):
        # For "forall" we add the variables to dummies and recurse.
        # TODO: rename dummy if its in target.free_variables(dummies) or
        # dummies.
        return try_rule_recursive(
            dummies.union(rule.get_variables(dummies)),
            rule[2],
            target,
            direction)

    if has_head(rule, Implies):
        # For ==>, if we're working backwards from the conclusion, we see if we
        # can match the RHS, and if so, we return the LHS, with appropriate
        # substitutions and free variables.  If we're working forwards, we match
        # the LHS and substitue on the RHS.
        if direction == Direction.BACKWARD:
            return match_and_substitute(dummies, rule[2], rule[1], target)
        elif direction == Direction.FORWARD:
            return match_and_substitute(dummies, rule[1], rule[2], target)

    if has_head(rule, Equivalent) or has_head(rule, Equal):
        return recursive_match_and_substitute(
            dummies, rule[2], rule[1], target).union(
            recursive_match_and_substitute(
                dummies, rule[1], rule[2], target))

    return set()


def match_and_substitute(dummies, to_match, replacement, target: Expression):
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


def is_instance(expr: Expression, rule: Expression, dummies=set()):
    """Determines whether 'expr' an instance of 'rule.'

    returns the substitution that makes them match, or None if there's no match.

    NOTE: Doesn't handle ForAll that's under anything other than more ForAlls.
    """

    assert isinstance(expr, Expression)
    assert isinstance(rule, Expression)

    if has_head(rule, ForAll):
        rule = cast(CompositeExpression, rule)
        return is_instance(
            expr, rule[2],
            dummies.union(rule.get_variables(dummies)))
    else:
        return match(dummies, rule, expr)


def substitute(subs, expr):
    """Given an expression, and a hash from vars to subexpressions,
    substitute the
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


# Returns the number of edges between node1 and node2.  For example, in
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


def collect_path(start: ExprAndParent) -> List[Expression]:
    ret = []
    while start is not None:
        assert isinstance(start, ExprAndParent)
        ret.append(start.expr)
        start = start.parent
    return ret


# Instead of just blindly trying everything, we should have a strategy, a goal
# to solve, and try whatever would help the goal.  What does that look like?
#
# So in the first problem, the goal is to prove P + Q in B.  And the only thing
# we know is the definition of B.
#
# From a purity point of view, I feel like the system should try all the rules
# and figure out for itself when they're useful and when they're not.  I guess
# we could start with some basic features, like what nodes are in it, even sub
# trees to pattern match against, and of course path length and other structural
# things.

def try_rules(context, goal, context_rules, general_rules, verbose=False):
    """context and context_rules are disjoint, all in context_rules satisfy
    is_rule(), whereas none of those in context do."""

    # We need to be able to recognize that the B in "P in B" is special, since
    # it only has meaning given by the rule, in fact by a single rule.  Hmm.
    # Should we think things like "+" and "in" are "general" and free variables
    # are "specific"?
    #
    # Whenever I try to come up with a principle like that, I feel like I'm
    # cheating.  In abstract algebra, "+" takes on a whole new meaning because
    # it follows a subset of the rules we know from real numbers.  So we have to
    # look at it with fresh eyes and it becomes "specific" again, until we get
    # an intuition about what you can do with it and what you can't.  And coming
    # up with that intuition is exactly what I want my system to do, some day.
    # But that no doubt involves parameter twiddling, and I want to avoid
    # parameter twiddling for now.  So that's the tension: I only want to
    # introduce parameter twiddling when I need it, yet I'm reluctant to try to
    # explicitly ossify my intution into a set of categories, for fear it will
    # constrain my thinking to that ontology.
    #
    # I do need to work incrementally toward my full system though. So at this
    # stage, I need my system to come up with adding the equations P * M == M *
    # P and Q * M == M * Q.  It could do that by noting some missing elements,
    # e.g. the goal has P, Q, M, * and +, and our context doesn't have a +.
    # There's also the symmetry: both the premises and the goal are symmetric in
    # P and Q, so we need to combine them in a symetric way.
    #
    # So we can start by simpling looking at the unqiue tokens we have,
    # recognizing that we need to combine our two premises and introduce a +.
    # So maybe I shouldn't fear that the simple ontology will become ossified.
    #
    # Working backwards from the goal, in the sense of applying the distributive
    # rule to it, is not bad either.  Neither is taking the LHS of the goal and
    # trying to transform it into the RHS.  In fact, I'd call that working
    # forward, in the important sense: you're not matching against the RHS of an
    # implies.

    # So the strategy is something like:
    #
    # - Try modifying the context in ways independent from the goal,
    #   e.g. simplifying, expanding definitions.
    #
    # - When that's done, try the same thing working backwards from the goal,
    #   independent of the context.
    #
    # - If the goal is a universally quantified equality, pick one side (for
    #   now, always the LHS) and try to transform it into the RHS by working
    #   forward.

    state = ProofState(context + context_rules, goal, general_rules, Exprs,
                       verbose)

    while True:
        made_progress = False
        # Step 1: apply context_rules to context_list.
        for cont in state.context.immediate_non_rules():
            print("*** Forward ***  " + str(cont.expr))
            for rule in state.context.immediate_rules():
                print("Rule: " + str(rule.expr))
                found = state.try_rule(
                    rule.expr,
                    cont,
                    state.context,
                    state.goals,
                    Direction.FORWARD)
                if isinstance(found, tuple):
                    return list(reversed(collect_path(
                        found[0]))) + collect_path(found[1])
                else:
                    made_progress |= found

        # Step 2: simplification / transformations from the goal.
        for goal in cast(Exprs, state.goals).immediate_non_rules():
            print("*** Backward ***  " + str(goal.expr))
            for rule in state.context.immediate_rules():
                found = state.try_rule(
                    rule.expr,
                    goal,
                    state.goals,
                    state.context,
                    Direction.BACKWARD)
                if isinstance(found, tuple):
                    return []  # TODO: Fill me in.
                else:
                    made_progress |= found

        if not made_progress:
            break

    while True:
        # Now, for each goal that's a possibly universally quantified equality,
        # grab the LHS and try to transform it into the RHS.
        for goal in cast(Exprs, state.goals).equalities():
            made_progress = False

            assert has_head(goal.expr, Equal)
            goal_expr = cast(CompositeExpression, goal.expr)
            lhs = ExprAndParent(goal_expr[1], goal.parent)
            targets = {goal_expr[2]: ExprAndParent(goal_expr[2], goal.parent)}
            print('*** goal: ' + str(goal.expr) + ', LHS: ' + str(lhs.expr) +
                  ', target: ' + str(next(iter(targets))))

            # So, (P + Q) * M is successfully transfomred into
            # P * M + Q * M.  We need to add that to the Exprs and try again.
            # We almost need a recursive call, trying the forward and backward
            # steps from above?  But only on expressions in temp_context.  We
            # still want to check against all expressions / rules.  But when
            # looping over non_rules(), we only want that to return the
            # immediate context's rules, not recurse to parent.
            temp_context = Exprs([goal_expr[1]], state.context)
            for rule in state.context.all_rules():
                found = state.try_rule(rule.rule.expr, lhs, temp_context,
                                       targets, Direction.BOTH)
                if isinstance(found, tuple):
                    return list(reversed(collect_path(
                        found[0]))) + collect_path(found[1])
                else:
                    made_progress |= found

            if not made_progress:
                break
        break

    print('************************  Final context:')
    print('\n'.join([str(v) for v in state.context]))
    print('************************  Final goals:')
    print('\n'.join([str(v) for v in state.goals]))

    return []


def try_rules_brute_force(context, goal, rules, verbose=False):
    state = ProofState(context, goal, rules, GoalExprsBruteForce, verbose)

    for iteration in range(1000):
        checked_all = True
        rule_index = 0

        if verbose:
            print('+++++++++++++++  Pass ' + str(iteration))

        all_rules = state.context.all_rules()
        while rule_index < len(all_rules):
            rule_pos = all_rules[rule_index]
            # rule_pos = rules[rule_index]
            assert rule_pos.premise <= len(state.context.all_non_rules())
            assert rule_pos.target <= len(state.goals.all_exprs())

            if verbose:
                print('********** Rule: ' + str(rule_pos))

            # Work forward from the context.
            if rule_pos.premise < len(state.context.all_non_rules()):
                checked_all = False
                print('context index: ' + str(rule_pos.premise))
                context_expr = state.context.all_non_rules()[rule_pos.premise]
                found = state.try_rule(
                    rule_pos.rule.expr,
                    context_expr,
                    state.context,
                    state.goals,
                    Direction.FORWARD)
                if isinstance(found, tuple):
                    return list(reversed(collect_path(found[0]))) + \
                           collect_path(found[1])

                print('New context: ' + str(state.context))
                print('context non rules: ' + str(
                    state.context.all_non_rules()))
                print('context relevant rules: ' +
                      str(state.context.immediate_rules()))
                rule_pos.premise += 1

            # Try working backward from goal.
            if rule_pos.target < len(state.goals.all_exprs()):
                checked_all = False
                goal_expr = state.goals.all_exprs()[rule_pos.target]
                assert isinstance(goal_expr, ExprAndParent)
                found = state.try_rule(
                    rule_pos.rule.expr,
                    goal_expr,
                    state.goals,
                    state.context,
                    Direction.BACKWARD)
                if isinstance(found, tuple):
                    assert isinstance(found, tuple)
                    assert isinstance(found[0], ExprAndParent)
                    assert isinstance(found[1], ExprAndParent)

                    return list(reversed(collect_path(found[1]))) + \
                        collect_path(found[0])

                rule_pos.target += 1

            rule_index += 1

        if checked_all:
            print("##########  Couldn't prove.")
            return None

    print("##########  Ran out of iterations.")
    return None


'''
def blah():
    import Parser

    def ex(input):
        return Parser.parse(input)

    A = var('A')
    M = var('M')
    B = var('B')
    P = var('P')
    Q = var('Q')
    R = var('R')

    mult_associative = forall((P, Q, R), ex('(P * Q) * R == P * (Q * R)'))

    # Multiplication distributes over addition
    left_dist = forall((P, Q, R), ex('R * (P + Q) == R * P + R * Q'))
    right_dist = forall((P, Q, R), ex('(P + Q) * R == P * R + Q * R'))

    # This is the definition of B:
    defB = forall(P, ex('P in B <==> P * M == M * P'))

    general_rules = [left_dist, right_dist, mult_associative]

    proof = try_rules([ex('P in B'), ex('Q in B')], ex('P + Q in B'),
                      [defB], general_rules, True)
'''
