class Expression:
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

    def __neq__(self, other):
        return not self.__eq__(other)


class CompositeExpression(Expression, tuple):
    # We need a shorter name for this.  Just "Composite"?  That
    # collides with the name for non-prime numbers.  "Internal"?
    # "Tree"?  "Cons"?  "Cells"?  "List"?  In Mathematica, a list is a
    # composite expression with head List.

    # I'm using inheritence instead of composition.  Oh well.
    def __repr__(self):
        assert(len(self) > 0)
        return self[0].repr_tree(self[1:])


class Node(Expression):
    # Mathematica calls this an Atom.  In Mathematica, Head of a node is
    # its type.  Seems non-orthogonal.

    def repr_tree(self, args):
        return repr(self) + '(' + ', '.join([repr(arg) for arg in args]) + ')'

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
    def __init__(self, name):
        self.name = name
        self.name_with_spaces = ' ' + name + ' '

    def repr_tree(self, args):
        return "(" + self.name_with_spaces.join([str(arg)
                                                 for arg in args]) + ")"


class Multiply(Infix):
    def __init__(self):
        Infix.__init__(self, '*')


class Divide(Infix):
    def __init__(self):
        Infix.__init__(self, '/')


class Sum(Infix):
    def __init__(self):
        Infix.__init__(self, '+')


class Difference(Infix):
    def __init__(self):
        Infix.__init__(self, '-')


class Element(Infix):
    def __init__(self):
        Infix.__init__(self, r'\in')


class Equivalent(Infix):
    def __init__(self):
        Infix.__init__(self, '<==>')
#        Infix.__init__(self, r'\iff')


class Implies(Infix):
    def __init__(self):
        Infix.__init__(self, '==>')
#        Infix.__init__(self, r'\implies')


class And(Infix):
    def __init__(self):
        Infix.__init__(self, 'and')


class Or(Infix):
    def __init__(self):
        Infix.__init__(self, 'or')


class Not(Node):
    def __repr__(self):
        return 'not'


class Equal(Infix):
    def __init__(self):
        Infix.__init__(self, '==')


class ForAll(Node):
    def __repr__(self):
        return r'\forall'


class Exists(Node):
    def __repr__(self):
        return r'\exists'


class Variable(Node):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return self.name == other.name

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
