from Expression import *
import Parser
from Deduction import *


def ex(input):
    return Parser.parse(input)


# Helpful for testing / debugging.  I should remove this at some point.
x = var('x')
y = var('y')
z = var('z')

# Problem 0.1.2 from Dummit and Foote "Abstract Algebra."
# M = (1  1; 0 1) (zero in lower left)
A = var('A')
M = var('M')
B = var('B')
P = var('P')
Q = var('Q')
R = var('R')

# A basic rule about + and ==.  It's interesting that this rule is already
# embedded in the pattern matching / substitution engine, but not in this
# explicit form: if you have a rule 'y == z', and your target is 'x + y', it
# will transform it to 'x + z', yet without the following rule it can't
# manipulate x + y == x + z.
add_to_both_sizes = forall([x, y, z], ex('y == z <==> x + y == x + z'))

# Multiplication is distributive
left_dist = forall([P, Q, R], ex('R * (P + Q) == R * P + R * Q'))
right_dist = forall([P, Q, R], ex('(P + Q) * R == P * R + Q * R'))

# This is the definition of B:
defB = forall(P, ex('P in B <==> P * M == M * P'))

# This is what we have to prove:
to_prove = forall([P, Q], ex('P in B and Q in B ==> P + Q in B'))


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


s = try_rule(set(), defB, in_(P + Q, B))
# (P + Q) * M == M * (P + Q)
print("** Substitution from rule: " + str(s))

# Next: apply the left & right distributitve laws.
# P * M + Q * M == M * P + M * Q
# Apply P \in B:
# M * P + Q * M == M * P + M * Q

# We could add some tautologies, like:
# forall X: X = X
# forall x, Y, Z: X + Y == X + Z <==> Y == Z


# Random Design Notes
#
#############
# Sage
#
# Well, Sage is potentially back in the running.  Sage symbolic
# expressions (sage.symbolic.Expression) have a base class
# sage.structure.Element, which has a base class
# sage.structure.SageObject, which is extensible.  Every object has a
# "parent" field, which is a metaclass, allowing you to mix
# expressions from different packages.
#
# Sage symbolic expressions are a wrapper around Pari/GP, which can do
# symbolic differentiation.  They don't have boolean expressions or
# first order logic, but it should be possible to add those in a way
# that will mix with symbolic expressions.  And it should be faster,
# since its Cython and they put a lot of effort into avoiding function
# dispatch overhead wherever possible.
#
# Earlier Sage notes:
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
# Should node have children, or should we separate node & tree structure?
#
# I think I need two diffferent kinds of equal, "node equal" and
# "tree equal," the second one recurses.  But for testing whether a
# node is in dummies, it would be really helpful to use "in".  In
# general, we'll want a hash table from nodes to all expressions which
# contain that node.  All this suggests having node objects that don't
# have children, and having a separate list structure to put them all
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

#############
# Types
#
# Even in my first example, I have two types: boolean and matrix.
# They have different operators, so you can tell their type from
# context, i.e. <==> is only for booleans, == is only for matricies.
# So I haven't taught my system about types yet, but its a bit of a
# house of cards, e.g. a rule X == X + 0 could get applied to an X
# that happens to be boolean, or P and Q ==> P to a matrix.  I'll need
# types before long.  How best to implement them?
