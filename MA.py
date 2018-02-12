# To check & run:
#
# coverage run --branch test_MA.py && coverage report --show-missing
# mypy .
# python3 MA.py

# What language should I ultimately do this in?
#
# Actual mathematicians / scientists only use Mathematica and Sage, not Coq or
# OCaml or anything so "exotic."  Plus, although Coq is great for logic and
# theorm proving, it can't do "regular" math, e.g. differentiate, find poles,
# etc.  So, I think I need to add theorem proving to Mathematica or Sage.
#
# Mathematica is sucks as a general programming language.  It doesn't have
# structures.  You can simulate them, kinda, with an (unevaluted) function of
# the form MyType[field1, field2].  Then you can make helper functions,
# e.g. Field1[x_MyType] = (some way to get the first arg).  But its kind of
# hacky, its non standard, there's no inheritence, there's no static checking,
# etc.
#
# So I guess Sage is the way to go.  That's a shame, because Coq has a great
# foundation for the logic / proof side of what I want to do.  And I like OCaml
# better as a language than Python.  Oh well.
#
# A Google search confirms there's no theorm proving library for Sage, and no
# interface to call Coq.  I suppose I could always call into Coq from Sage?
# Recreating Coq in Sage would be fun, but seems like a lot of busy work,
# and wouldn't incorporate any improvements done to Coq.

import Parser
from Deduction import *


def ex(st):
    return Parser.parse(st)


# Helpful for testing / debugging.  I should remove this at some point.
a = var('a')
b = var('b')
c = var('c')
d = var('d')

p = var('p')
q = var('q')
r = var('r')
s = var('s')

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

# Rules for equals
equals_reflexive = forall(x, ex('x == x'))

# Multiplication is associative
mult_associative = forall((P, Q, R), ex('(P * Q) * R == P * (Q * R)'))

# Multiplication distributes over addition
left_dist = forall((P, Q, R), ex('R * (P + Q) == R * P + R * Q'))
right_dist = forall((P, Q, R), ex('(P + Q) * R == P * R + Q * R'))

# This is the definition of B:
defB = forall(P, ex('P in B <==> P * M == M * P'))


general_rules = [left_dist, right_dist, mult_associative]

proof = try_rules_brute_force([ex('P in B'), ex('Q in B')], ex('P + Q in B'),
                              [defB] + general_rules, True)
if proof:
    for expr in proof:
        print(expr)

# print('&&&&&&&&&&&  "Smart" Implementation  &&&&&&&&&&')
#
#
# proof = try_rules([defB, ex('P in B'), ex('Q in B')], ex('P + Q in B'),
#                   general_rules, True)
#
# if not proof:
#     exit(1)
#
# for p in proof:
#     print(p)


# So, what we're calling 'rules' here aren't actually rules but axioms,
# i.e. within the context of this problem, they're like premeses.  The only
# actual rules we have at the moment are modus ponens and 'equal substitution.'

rules = [defB, left_dist, right_dist, mult_associative]  # , equals_reflexive]

# Dummit and Foote, problem 0.1.2
print('\n\n**********  Problem 0.1.2')
proof = try_rules([defB, ex('P in B'), ex('Q in B')],
                  ex('P + Q in B'), general_rules, True)
if not proof:
    exit(1)

for step in proof:
    print(step)

# Dummit and Foote, problem 0.1.3
print('\n\n**********  Problem 0.1.3')
proof = try_rules([defB, ex('P in B'), ex('Q in B')],
                  ex('P * Q in B'), general_rules, True)
if not proof:
    exit(1)

for step in proof:
    print(step)

# Now that we have matrix literals:

# Dummit and Foote, problem 0.1.1:
print('\n\n**********  Problem 0.1.1')
# "Let A bet the set of 2 x 2 matrices with real number entries."
# "Determine which of the following elements of A line in B:
# [1 1; 0 1]   [1 1; 1 1]   [0 0; 0 0]   [1 1; 1 0]   [1 0; 0 1]   [0 1; 1 0]

mat_mult = forall((a, b, c, d, p, q, r, s),
                  ex('[a b; c d] * [p q; r s] =='
                     '   [a * p + b * r   a * q + b * s;'
                     '    c * p + d * r   c * q + d * s]'))
defM = ex('M == [1 1; 0 1]')


def helper(context, goal, general_rules, verbose=True):
    proof = try_rules(context, goal, general_rules, verbose)

    if not proof:
        exit(1)

    print("*****  Found solution!  *****")
    for step in proof:
        print(step)


def helper_0_1_1(defX):
    print('!!!!! ' + str(defX))
    helper(context=[defB, defM, defX], goal=ex('X in B'),
           general_rules=general_rules + [mat_mult], verbose=True)

# How do we want to solve this?  We could notice that M == X, so that the
# condition X in B becomes X * M == M * X, which is just M * M == M * M,
# which is true by reflexivity.

# Noticing M == X is interesting.  The current code only does it indirectly:
# after substituting [1 1; 0 1] for X in some expression, it can then
# substitute M for that.  I don't think it has a way to actually generate X
# == M and add that to the premises.  So what's needed?
#
# Notice that that pair of transforms often happens together and chunk it?
# Notice that we often use variables to substitute for larger expressions?
# Notice that we get X * M == M * X, and look for connections between X and M?

# I definitely need ways to represent subgoals, etc. in my output of proofs.


helper_0_1_1(ex('X == [1 1; 0 1]'))

helper_0_1_1(ex('X == [1 1; 1 1]'))
helper_0_1_1(ex('X == [0 0; 0 0]'))
helper_0_1_1(ex('X == [1 1; 1 0]'))
helper_0_1_1(ex('X == [1 0; 0 1]'))
helper_0_1_1(ex('X == [0 1; 1 0]'))

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
# Even in my first example, I have three types: boolean, matrix and logical
# connective, i.e. function from bool x bool -> bool.
# They have different operators, so you can tell their type from
# context, i.e. <==> is only for booleans, == is only for matricies.
# So I haven't taught my system about types yet, but its a bit of a
# house of cards, e.g. a rule X == X + 0 could get applied to an X
# that happens to be boolean, or P and Q ==> P to a matrix.  I'll need
# types before long.  How best to implement them?
