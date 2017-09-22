# Notes in google docs, "How do you discover / learn algebra?"

# Possible yak shaving tasks:
# - Implement more operators, including parsing & printing.
# - Implement integer literals, including parsing & printing.
# - DRY the parser, at least the Infix part.
# - Write tests for the "pragma: no cover" comments in this source file
#   (Expression.py), then remove the comments.
# - Convert to Coq's notation:
#   forall
#   -> (implies, although also has => for defining functions)
# - An iterator that allows looping over a list while we're appending to it.
# - Change try_rule*() to only take a single "context", the union of the current
#   context and context_rules, and partition based on is_rule.
# - Add more types.

# - Have unit (integration?) tests for the theorm prover.  Most general is that
#   each step is logically valid.  We'd need a better representation of the
#   proof though, a tree rather than a list.  More specific is that the proof is
#   minimal, or near minimal, or doesn't have any obviously uneeded steps, etc.


from enum import Enum, unique
from functools import total_ordering
from pprint import pprint
from abc import ABCMeta, abstractmethod
from collections import Hashable
from typing import AbstractSet


@total_ordering
@unique
class Precedence(Enum):
    # This is only used for pretty-printing, not parsing, but needs to be kept
    # in sync with parser in Parser.py.

    # We should only use the ordering of these, not the actual value, because
    # the values will change as we add more operators.
    FORALL_EXISTS = 1
    IMPLIES_EQUIV = 2
    AND_OR = 3
    NEGATION = 4
    COMPARISON = 5
    ADDITIVE = 6
    MULTIPLICATIVE = 7
    FUNCALL = 8
    ATOM = 9

    def __lt__(self, other):
        return self.value < other.value


class Expression:
    # We should consider getting rid of __mul__ and __add__.  They're used in
    # unit tests of the parser, but would be easy to replace with functions.
    def __mul__(self, rhs):
        return CompositeExpression([Multiply(), self, rhs])

    # "+" already means "concatenate" for lists.  But concatenating
    # argument lists seems much rarer than constructing expressions
    # using "+", especially in abstract algebra.
    def __add__(self, rhs):
        return CompositeExpression([Sum(), self, rhs])

    # I considered doing the Sage thing and overriding __eq__ and other "rich
    # comparison operators" to return symbolic expressions.  Sage then overrides
    # __nonzero__ to evaluate the comparison.  Sage's evaluation does search to
    # see if things are equal, e.g. assert((x-1)^2 == x^2 - 2*x + 1).  So its
    # compute intensive, not something you want in the inner loop of your
    # pattern matching.  Sage also searches assumptions when comparing leaves,
    # e.g. if you assume(x == y), then bool(x == y) evaluates to True.
    #
    # So instead I left __eq__ to mean syntactic equality, so it can be used
    # during pattern matching.  And I implemented a separate parser, which
    # allows me to have "and," "or" and "not" as infix operators, along with ==>
    # and <==>

    def __repr__(self):
        return self.repr_and_precedence()[0]

    @abstractmethod
    def free_variables(self, exclude)-> AbstractSet['Variable']:
        return set()  # pragma: no cover

    # TODO: Have all missing methods forward to their first argument, so we
    # don't need the boilerplate here?
    def get_variables(self, other_dummies):
        return self[0].get_variables(self, other_dummies)


class CompositeExpression(Expression, tuple):
    # We need a shorter name for this.  Just "Composite"?  That
    # collides with the name for non-prime numbers.  "Internal"?
    # "Tree"?  "Cons"?  "Cells"?  "List"?  In Mathematica, a list is a
    # composite expression with head List.

    def __init__(self, iter):
        lst = [it for it in iter]
        for it in lst:
            assert isinstance(it, Hashable)
        tuple.__init__(lst)

    # I'm using inheritence instead of composition.  Oh well.
    def repr_and_precedence(self):
        assert(len(self) > 0)
        return self[0].repr_tree(self[1:])

    # Call pprint.pprint() on result.
    def declass(self):  # pragma: no cover
        """Intended for debugging, shows the structure of the tree, even for
        invalid trees.
        """
        return [e.declass() for e in self]

    def free_variables(self, exclude) -> AbstractSet['Variable']:
        return {var for child in self for var in child.free_variables(exclude)}


class Node(Expression):
    # Mathematica calls this an Atom.  In Mathematica, Head of a node is
    # its type.  Seems non-orthogonal.

    def repr_and_precedence(self):
        return (repr(self), Precedence.ATOM)

    # Currently, our parser can't generate these.
    def repr_tree(self, args):
        return (repr(self) +
                '(' +
                ', '.join([repr(arg) for arg in args]) +
                ')', Precedence.FUNCALL)

    def __eq__(self, other):
        return isinstance(self, type(other))

    def __hash__(self):
        return hash(type(self))

    # Handy utilitiy function used by repr_tree in some children.
    def wrap(self, child_repr_and_precedence):
        rep, child_prec = child_repr_and_precedence
        return rep if child_prec > self.precedence else '(' + rep + ')'

    def __repr__(self):
        # If we really are an atom, our derived class needs to implement this.
        # If we're an operator, this shouldn't be called.
        raise NotImplementedError  # pragma: no cover

    def declass(self):  # pragma: no cover
        return type(self).__name__

    # Returns a set().
    def free_variables(self, exclude):
        return set()


# I disagree with Python's "ask forgiveness, not permission" ethos, at
# least for this sort of mathematical pattern matching code.
def has_head(expr: Expression, clz: type) -> bool:
    """
    :rtype: bool
    """
    assert isinstance(expr, Expression)
    assert isinstance(clz, type)
    return isinstance(expr, CompositeExpression) and isinstance(expr[0], clz)


# Name relations after nouns or adjectives, not verbs: Equal, not Equals; Sum,
# not Add.

class Infix(Node):
    def __init__(self, name, precedence):
        assert isinstance(precedence, Precedence)
        self.name = name
        self.name_with_spaces = ' ' + name + ' '
        self.precedence = precedence

    def repr_tree(self, args):
        return (self.name_with_spaces.join(
            [self.wrap(arg.repr_and_precedence()) for arg in args]),
            self.precedence)


class Prefix(Node):
    def __init__(self, name, precedence):
        assert isinstance(precedence, Precedence)
        self.name = name
        self.name_with_space = name + ' '
        self.precedence = precedence

    def repr_tree(self, args):
        assert len(args) == 1
        return (
            self.name_with_space + self.wrap(args[0].repr_and_precedence()),
            self.precedence)


class Multiply(Infix):
    def __init__(self):
        Infix.__init__(self, '*', Precedence.MULTIPLICATIVE)


class Divide(Infix):
    def __init__(self):  # pragma: no cover
        Infix.__init__(self, '/', Precedence.MULTIPLICATIVE)


class Sum(Infix):
    def __init__(self):
        Infix.__init__(self, '+', Precedence.ADDITIVE)


class Difference(Infix):
    def __init__(self):  # pragma: no cover
        Infix.__init__(self, '-', Precedence.ADDITIVE)


class Element(Infix):
    def __init__(self):
        Infix.__init__(self, r'\in', Precedence.COMPARISON)


class Equivalent(Infix):
    def __init__(self):
        Infix.__init__(self, '<==>', Precedence.IMPLIES_EQUIV)
#        Infix.__init__(self, r'\iff')


class Implies(Infix):
    def __init__(self):
        Infix.__init__(self, '==>', Precedence.IMPLIES_EQUIV)
#        Infix.__init__(self, r'\implies')


class And(Infix):
    def __init__(self):
        Infix.__init__(self, 'and', Precedence.AND_OR)


class Or(Infix):
    def __init__(self):
        Infix.__init__(self, 'or', Precedence.AND_OR)


class Not(Prefix):
    def __init__(self):
        Prefix.__init__(self, 'not', Precedence.NEGATION)


class Equal(Infix):
    def __init__(self):
        Infix.__init__(self, '==', Precedence.COMPARISON)


class Quantifier(Node):
    def get_variables(self, expr, other_dummies):
        if isinstance(expr[1], Node):
            assert expr[1] not in other_dummies
            return {expr[1]}
        else:
            assert other_dummies.isdisjoint(expr[1])
            return expr[1]


class ForAll(Quantifier):
    def __repr__(self):
        return r'\forall'


class Exists(Quantifier):
    def __repr__(self):
        return r'\exists'


class Variable(Node):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Variable) and self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def declass(self):  # pragma: no cover
        return self.name

    # Returns a set().
    def free_variables(self, exclude) -> AbstractSet['Variable']:
        if self in exclude:
            return set()
        else:
            return {self}


def makefn(clz, name=''):
    def maker(*args):
        return CompositeExpression([clz()] + list(args))
    maker.__name__ = name if name else clz.__name__.lower()
    return maker


# You can use these handy functions to construct nodes, or the Parser below.
multiply = makefn(Multiply)
sum = makefn(Sum)
equal = makefn(Equal)
forall = makefn(ForAll)
exists = makefn(Exists)
implies = makefn(Implies)
equivalent = makefn(Equivalent)
element = makefn(Element)
and_ = makefn(And, 'and_')
or_ = makefn(Or, 'or_')
not_ = makefn(Not, 'not_')


def var(name):
    return Variable(name)


def iff(left, right):
    return equivalent(left, right)


def in_(left, right):
    return element(left, right)
