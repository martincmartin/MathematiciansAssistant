class Expression:
    def __mul__(self, rhs):
        return CompositeExpression([Multiply(), self, rhs])

    # "+" already means "concatenate" for lists.  But concatenating
    # argument lists seems much rarer than constructing expressions
    # using "+", especially in abstract algebra.
    def __add__(self, rhs):
        return CompositeExpression([Sum(), self, rhs])

    def __neq__(self, other):
        return not self.__eq__(other)


class CompositeExpression(Expression, list):
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
        return type(self) == type(other)

    def __hash__(self):
        return hash(type(self))


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


class Sum(Infix):
    def __init__(self):
        Infix.__init__(self, '+')


class Element(Infix):
    def __init__(self):
        Infix.__init__(self, r'\in')


class Equivalent(Infix):
    def __init__(self):
        Infix.__init__(self, r'\iff')


class Implies(Infix):
    def __init__(self):
        Infix.__init__(self, r'\implies')


class And(Infix):
    def __init__(self):
        Infix.__init__(self, 'and')


class Or(Infix):
    def __init__(self):
        Infix.__init__(self, 'or')


class Not(Node):
    def __repr__(self):
        return 'not'


class Equals(Infix):
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


multiply = makefn(Multiply)
sum = makefn(Sum)
equals = makefn(Equals)
forall = makefn(ForAll)
implies = makefn(Implies)
equivalent = makefn(Equivalent)
element = makefn(Element)
and_ = makefn(And, 'and_')
or_ = makefn(Or, 'or_')


def var(name):
    return Variable(name)


def iff(left, right):
    return equivalent(left, right)


def in_(left, right):
    return element(left, right)



# Helpful for testing / debugging.  I should remove this at some point.
x = var('x')
y = var('y')
z = var('z')

# Problem 0.1.2 from Dummit and Foote "Abstract Algebra."
A = var('A')
M = var('M')
B = var('B')
P = var('P')
Q = var('Q')
R = var('R')

# Multiplication is distributive
leftDist = forall([P, Q, R], equals(R * (P + Q), R * P + R * Q))
rightDist = forall([P, Q, R], equals((P + Q) * R, P * R + Q * R))

# This is the definition of B:
defB = forall(P, iff(in_(P, B), equals(P * M, M * P)))

# This is what we have to prove:
toprove = forall([P, Q], implies(and_(in_(P, B), in_(Q, B)), in_(P + Q, B)))

print(leftDist)
print(rightDist)
print(defB)
print(toprove)

# So the idea is that we have a search problem, like GOFAI.  For
# example, at this point, all we know about the set B is its
# definition, so the only thing we can do to either the premise or
# conclusion of our (in-progress) proof is to expand them based on the
# definition.
#
# Later, we can worry about what happens when we have lots of options.
#
# So, to prove an "implies", you search for a path from the start
# (plus other premises) to the end.  In fact, the start may be a red
# herring, so for now we can focus on the end.

# We need some pattern matching.
#
# We start with P + Q \in B, and want to find all rules which match it.
#
# This is where overriding == might be killing me?  Well, I think I
# need two diffferent kinds of equals, "node equals" and "tree
# equals," the second one recurses.  But for testing whether a node is
# in dummies, it would be really helpful to use "in".  In general,
# we'll want a hash table from nodes to all expressions which contain
# that node.  All this suggests having node objects that don't have
# children, and having a separate list structure to put them all
# together.  Like LISP and Mathematica...  But that's not object
# oriented!  :) Well, maybe we don't want object oriented for the
# structure?  If we're doing pattern matching, the tree structure is
# pretty fundamental.  And I think all of mathematics can fit in the
# tree structure?  For example, does LaTeX make that assumption?  Of
# course, LaTeX only has to display math, it doesn't include
# semantics, so it can probably cheat.
#
# What is node_eq used for?  Pattern matching, and that's about it I
# guess.  So am I driving my design based on a special case?
# Mathematica allows the "head" (what I'm calling the node) to
# actually be a subtree.  This allows you to write f(x)(y).  In a
# traditional programming language, you'd have a "function call" node
# in the AST, so you'd also end up with the function being a child of
# that node.  Ok, let's do that then.


# Returns the substitution (as dict) that makes them match, or None if
# there's no match.  Be careful: both the empty dict (meaning there's
# a match that works with any substitution) and None (they don't match
# no matter what you substitue) evaluate as false in Python.
def match(dummies, pattern, target):
    if isinstance(pattern, Node):
        if pattern in dummies:
            return {pattern: target}
        if pattern == target:
            return {}
        return None

    assert isinstance(pattern, CompositeExpression)

    # TODO: Allow something akin to *args, a pattern that matches any
    # number of remaining args.
    if len(pattern) != len(target):
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
                if ret[k] != v:
                    return None
        ret.update(m)
    return ret

# Random Design Notes
#
#############
# Not Using Sage
#
# Sage symbolic boolean expressions don't mix with sage symbolic
# algebra expressions.  And it doesn't seem to have first order logic
# constructs like "for all."  It doesn't do much symbolic manipulation
# on its own, instead it hands expressions off to other packages like
# Maxima to do the symbol manipulation.  It seems to have a different
# representation for every subdomain, and you can't create trees that
# mix them.  In general, it seems really poor for the theorem proving
# stuff I'm trying to do.  So I'm ditching Sage.  Should probably go
# with Mathematica, but will stay with a general programming language
# as long as possible.
#
#############
# How To Indicate Pattern Match (universally quantified) variables
#
# Explicit scoping of free variables, vs. Mathematica's trailing
# underscore, versus having a different type (e.g. var('P') declares
# generic variables that are implcitly forall at the start of any
# expression, whereas some other construct, say const('B') means that
# B is the same in all expressions.)
#
# We still need to worry about free vs bound variables and renaming.
# Maybe we should consider all un-bound variables to be universally
# quantified over the expression?  Or maybe we can be explicit about
# quantification for now.  Fun with first order logic!
#
# It seems Mathematica doesn't have unification, only pattern
# matching.  I should be able to do pattern matching in Python without
# too much trouble.  I could use the Mathematica convention that a
# trailing underscore on a vairable name means universal
# quantification within the rewrite rule.
#
# Nah, go for explicit quantification for now.
#############
