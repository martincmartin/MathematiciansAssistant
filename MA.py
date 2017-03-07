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

    def __str__(self):
        return "(" + self.name_with_spaces.join([str(child)
                                                 for child in self.children]) + ")"


class Prefix(Expression):
    def __init__(self, name, *args):
        Expression.__init__(self, *args)
        self.name = name

    def __str__(self):
        return self.name + \
            "(" + ', '.join([str(child) for child in self.children]) + ")"


class Multiply(Infix):
    def __init__(self, *args):
        Infix.__init__(self, '*', *args)


class Sum(Infix):
    def __init__(self, *args):
        Infix.__init__(self, '+', *args)


class ElementOf(Infix):
    def __init__(self, *args):
        Infix.__init__(self, '\in', *args)


class EquivalentTo(Infix):
    def __init__(self, left, right):
        Infix.__init__(self, '\iff', left, right)


class Implies(Infix):
    def __init__(self, left, right):
        Infix.__init__(self, '\implies', left, right)


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


class Variable(Expression):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name


def var(name):
    return Variable(name)


def in_(left, right):
    return ElementOf(left, right)


def iff(left, right):
    return EquivalentTo(left, right)


def and_(left, right):
    return And(left, right)


def or_(left, right):
    return Or(left, right)


def implies(left, right):
    return Implies(left, right)


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
leftDist = R * (P + Q) == R * P + R * Q
rightDist = (P + Q) * R == P * R + Q * R

# This is the definition of B:
defB = iff(in_(P, B), P * M == M * P)

# This is what we have to prove:
toprove = implies(and_(in_(P, B), in_(Q, B)), in_(P + Q, B))
