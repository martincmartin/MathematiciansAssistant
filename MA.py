# Sage symbolic boolean expressions don't mix with sage symbolic
# algebra expressions.  And it doesn't seem to have first order logic
# constructs like "for all."  It seems really poor for the theorem
# proving stuff I'm trying to do.  So I'm ditching Sage.  Should
# probably go with Mathematica, but will stay with a general
# programming language as long as possible.


# Not sure we need a base class for all expression types, but what the heck.
class Expression:
    def __init__(self, *args):
        # Not sure this should be in here.  Oh well.
        self.children = args

    def __mul__(self, rhs):
        return Multiply(self, rhs)

    def __add__(self, rhs):
        return Sum(self, rhs)

    # Overriding this is a little dangerous, since Python assumes it
    # returns a bool to test whether two Expressions are equal in a
    # lot of places.  But Sage seems to do it, so we'll see how much
    # trouble this gets us in.
    def __eq__(self, rhs):
        return Equals(self, rhs)

    def __ne__(self, rhs):
        # For now, no three valued logic.
        return Not(self == rhs)


class Infix(Expression):
    def __init__(self, name, *args):
        Expression.__init__(self, *args)
        self.name = name
        self.name_with_spaces = ' ' + name + ' '

    def __repr__(self):
        return "(" + self.name_with_spaces.join([str(child)
                                                 for child in self.children]) + ")"


class Prefix(Expression):
    def __init__(self, name, *args):
        Expression.__init__(self, *args)
        self.name = name

    def __repr__(self):
        return self.name + \
            "(" + ', '.join([str(child) for child in self.children]) + ")"


class Multiply(Infix):
    def __init__(self, *args):
        Infix.__init__(self, '*', *args)


class Sum(Infix):
    def __init__(self, *args):
        Infix.__init__(self, '+', *args)


class Element(Infix):
    def __init__(self, *args):
        Infix.__init__(self, r'\in', *args)


class Equivalent(Infix):
    def __init__(self, left, right):
        Infix.__init__(self, r'\iff', left, right)


class Implies(Infix):
    def __init__(self, left, right):
        Infix.__init__(self, r'\implies', left, right)


class And(Infix):
    def __init__(self, *args):
        Infix.__init__(self, 'and', *args)


class Or(Infix):
    def __init__(self, *args):
        Infix.__init__(self, 'or', *args)


class Not(Prefix):
    def __init__(self, *args):
        Infix.__init__(self, 'not', *args)


class Equals(Infix):
    def __init__(self, *args):
        Infix.__init__(self, '==', *args)


class ForAll(Prefix):
    def __init__(self, vars_, expr):
        Prefix.__init__(self, r'\forall', vars_, expr)


class Exists(Prefix):
    def __init__(self, *args):
        Prefix.__init__(self, r'\exists', *args)


class Variable(Expression):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name


def var(name):
    return Variable(name)


def Iff(left, right):
    return Equivalent(left, right)


def In(left, right):
    return Element(left, right)



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
leftDist = ForAll([P, Q, R], R * (P + Q) == R * P + R * Q)
rightDist = ForAll([P, Q, R], (P + Q) * R == P * R + Q * R)

# This is the definition of B:
defB = ForAll(P, Iff(In(P, B), P * M == M * P))

# This is what we have to prove:
toprove = ForAll([P, Q], Implies(And(In(P, B), In(Q, B)), In(P + Q, B)))

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


# Random Design Notes
#
#############
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
