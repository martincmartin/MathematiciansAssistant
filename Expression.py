from enum import Enum, unique
from functools import total_ordering


# This is only used for pretty-printing, not parsing, but needs to be kept in
# sync with parser in Parser.py.
#
# We should only use the ordering of these, not the actual value, because the
# values will change as we add more operators.
@total_ordering
@unique
class Precedence(Enum):
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


class CompositeExpression(Expression, tuple):
    # We need a shorter name for this.  Just "Composite"?  That
    # collides with the name for non-prime numbers.  "Internal"?
    # "Tree"?  "Cons"?  "Cells"?  "List"?  In Mathematica, a list is a
    # composite expression with head List.

    # I'm using inheritence instead of composition.  Oh well.
    def repr_and_precedence(self):
        assert(len(self) > 0)
        return self[0].repr_tree(self[1:])


class Node(Expression):
    # Mathematica calls this an Atom.  In Mathematica, Head of a node is
    # its type.  Seems non-orthogonal.

    def repr_and_precedence(self):
        return (repr(self), Precedence.ATOM)

    def repr_tree(self, args):
        return (repr(self) +
                '(' +
                ', '.join([repr(arg) for arg in args]) +
                ')', Precedence.FUNCALL)

    def __eq__(self, other):
        return isinstance(self, type(other))

    def __hash__(self):
        return hash(type(self))


# I disagree with Python's "ask forgiveness, not permission" ethos, at
# least for this sort of mathematical pattern matching code.
def has_head(expr, clz):
    return isinstance(expr, CompositeExpression) and isinstance(expr[0], clz)


# Name relations after nouns or adjectives, not verbs: Equal, not Equals; Sum,
# not Add.

class Infix(Node):
    def __init__(self, name, precedence):
        assert isinstance(precedence, Precedence)
        self.name = name
        self.name_with_spaces = ' ' + name + ' '
        self.precedence = precedence

    def wrap(self, child_repr_and_precedence):
        rep, child_prec = child_repr_and_precedence
        return rep if child_prec > self.precedence else '(' + rep + ')'

    def repr_tree(self, args):
        return (self.name_with_spaces.join(
            [self.wrap(arg.repr_and_precedence()) for arg in args]),
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


class Not(Node):
    def __repr__(self):  # pragma: no cover
        return 'not'


class Equal(Infix):
    def __init__(self):
        Infix.__init__(self, '==', Precedence.COMPARISON)


class ForAll(Node):
    def __repr__(self):  # pragma: no cover
        return r'\forall'


class Exists(Node):
    def __repr__(self):  # pragma: no cover
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
