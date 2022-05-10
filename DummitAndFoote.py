# To check & run:
#
# coverage run --branch test_MA.py && coverage report --show-missing
# mypy .
# python3 MA.py

import Parser

# from DeductionOrig import *
from Expression import Expression, CompositeExpression, var, forall, ExpressionType

import DeductionApril2018

import sys

# import typeguard

from typing import Sequence

# Save some typing
OBJECT = ExpressionType.OBJECT


def ex(st: str) -> Expression:
    return Parser.parse(st)


def doit() -> None:
    # Helpful for testing / debugging.  I should remove this at some point.
    a = var("a", OBJECT)
    b = var("b", OBJECT)
    c = var("c", OBJECT)
    d = var("d", OBJECT)

    p = var("p", OBJECT)
    q = var("q", OBJECT)
    r = var("r", OBJECT)
    s = var("s", OBJECT)

    x = var("x", OBJECT)
    y = var("y", OBJECT)
    z = var("z", OBJECT)

    # Problem 0.1.2 from Dummit and Foote "Abstract Algebra."
    # M = (1  1; 0 1) (zero in lower left)
    A = var("A", OBJECT)
    M = var("M", OBJECT)
    B = var("B", OBJECT)
    P = var("P", OBJECT)
    Q = var("Q", OBJECT)
    R = var("R", OBJECT)

    # Rules for equals
    equals_reflexive: CompositeExpression = forall(x, ex("x == x"))

    # Multiplication is associative
    mult_associative: CompositeExpression = forall(
        (P, Q, R), ex("(P * Q) * R == P * (Q * R)")
    )

    # Multiplication distributes over addition
    left_dist: CompositeExpression = forall(
        (P, Q, R), ex("R * (P + Q) == R * P + R * Q")
    )
    right_dist: CompositeExpression = forall(
        (P, Q, R), ex("(P + Q) * R == P * R + Q * R")
    )

    # This is the definition of B:
    defB: CompositeExpression = forall(P, ex("P in B <==> P * M == M * P"))

    general_rules = [left_dist, right_dist, mult_associative]

    def helper(
        context: Sequence[Expression],
        goal: Expression,
        general_rules: Sequence[Expression],
        verbosity: int = 1,
    ) -> None:
        proof = DeductionApril2018.try_rules(context, goal, general_rules, verbosity)

        if not proof:
            exit(1)

        print("*****  Found solution!  *****")
        for step in proof:
            print(step)

    # proofbf = try_rules_brute_force([ex('P in B'), ex('Q in B')], ex('P + Q in B'),
    #                               [defB] + general_rules, False)
    # if proofbf:
    #     print("*****  Found solution!  *****")
    #     for expr in proofbf:
    #         print(expr)

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

    if True:
        # Dummit and Foote, problem 0.1.2
        print("\n\n**********  Problem 0.1.2")
        helper(
            [defB, ex("P in B"), ex("Q in B")],
            ex("P + Q in B"),
            general_rules,
            5,
        )

        # Dummit and Foote, problem 0.1.3
        print("\n\n**********  Problem 0.1.3")
        helper(
            [defB, ex("P in B"), ex("Q in B")],
            ex("P * Q in B"),
            general_rules,
            5,
        )

    # Now that we have matrix literals:

    # Dummit and Foote, problem 0.1.1:
    print("\n\n**********  Problem 0.1.1")
    # "Let A be the set of 2 x 2 matrices with real number entries.  Let M =
    # [1 1; 0 1] and let B = {X in A| MX = XM}."
    # "Determine which of the following elements of A lie in B:
    # [1 1; 0 1]   [1 1; 1 1]   [0 0; 0 0]   [1 1; 1 0]   [1 0; 0 1]   [0 1; 1 0]

    mat_mult = forall(
        (a, b, c, d, p, q, r, s),
        ex(
            "[a b; c d] * [p q; r s] =="
            "   [a * p + b * r   a * q + b * s;"
            "    c * p + d * r   c * q + d * s]"
        ),
    )
    mult_ident_l = forall(x, ex("1 * x == x"))
    mult_ident_r = forall(x, ex("x * 1 == x"))
    mult_zero_l = forall(x, ex("0 * x == 0"))
    mult_zero_r = forall(x, ex("x * 0 == 0"))
    add_ident_l = forall(x, ex("0 + x == x"))
    add_ident_r = forall(x, ex("x + 0 == x"))

    ident_and_zero = [
        mult_ident_l,
        mult_ident_r,
        mult_zero_l,
        mult_zero_r,
        add_ident_l,
        add_ident_r,
    ]

    defM = ex("M == [1 1; 0 1]")

    def helper_0_1_1(defX: Expression):
        print("!!!!! " + str(defX))
        helper(
            context=[defB, defM, defX],
            goal=ex("X in B"),
            general_rules=general_rules + [mat_mult] + ident_and_zero,
            verbosity=5,
        )

    # How do we want to solve this?  We could notice that M == X, so that the
    # condition X in B becomes X * M == M * X, which is just M * M == M * M,
    # which is true by reflexivity.

    # Noticing M == X is interesting.  The current code only does it indirectly:
    # after substituting [1 1; 0 1] for X in some expression, it can then
    # _substitute M for that.  I don't think it has a way to actually generate X
    # == M and add that to the premises.  So what's needed?
    #
    # Notice that that pair of transforms often happens together and chunk it?
    # Notice that we often use variables to _substitute for larger expressions?
    # Notice that we get X * M == M * X, and look for connections between X and M?

    # I definitely need ways to represent subgoals, etc. in my output of proofs.

    # Hey it proves this!
    helper_0_1_1(ex("X == [1 1; 0 1]"))
    # This one is false, and we don't have a way yet to prove that things are
    # false.
    # helper_0_1_1(ex("X == [1 1; 1 1]"))

    sys.exit(0)
    # This one is true, since both sides evaluate to the zero matrix.  But we
    # can't discover this, because (a) we produce a ton of distracting crap,
    # and (b) we only ever work forward, never backward.
    helper_0_1_1(ex("X == [0 0; 0 0]"))

    helper_0_1_1(ex("X == [1 1; 1 0]"))
    helper_0_1_1(ex("X == [1 0; 0 1]"))
    helper_0_1_1(ex("X == [0 1; 1 0]"))


doit()
sys.exit(0)

if __name__ == "__main__":
    with typeguard.TypeChecker(
        [
            "MA",
            "MatchAndSubstitute",
            "DeductionApril2018",
            "DeductionHelpers",
            "Expression",
        ]
    ):
        doit()

# Remembering what I was doing (delete this once I'm mentally unblocked):
#
# The current problem MA is trying to solve:
#
# X == [1 1; 1 1]
# M == [1 1; 0 1]
# \forall{P}(P \in B <==> P * M == M * P)
# Prove:
# X in B.
#
# It successfully transforms "X in B" into:
# "X * M == M * X"
#
# It then picks that as the goal, adds  X * M as a premise, and M * X as a goal.
#
# It then starts working forward, turns X * M into X * [1  1; 0  1] (and
# [1  1; 1  1] * M) in the first pass.  In the second pass, into
# [1  1; 1  1] * [1  1; 0  1].  In the third pass, into
# [1 * 1 + 1 * 0   1 * 1 + 1 * 1;  1 * 1 + 1 * 0   1 * 1 + 1 * 1].
#
# There are a couple problems.  The immediate one is that our premises are
# full of crap, stuff like \forall{_x, x}(X * [1  1; x * (_x * (0 * _x))
# 1]).  We get so bogged down with this, we can't make any progress.
#
# The longer term problem is that we're only working forward, not backward.
# So our set of goals never change, so even if we reduce the LHS (premise) to
# [1 2; 1 2], we'll never reduce the RHS M * X to anything, and factoring the
# LHS into M * X could prove tricky.  Also, this is a case where the matrix
# is *not* in the set, because M * X == [2 2; 1 1].  And the system can't
# currently recognize that.
#
# It does get awfully distracted by rules of the form A == B; it transforms
# them into A == A and B == B, then keeps applying them wherever it sees and
# A or a B.  Of course, those are all immediate dead ends, so it's not so
# bad.  Still, it may need to learn not to waste time on all this.
#
# So what do we do?  Go back to middle school and work with single variable
# equations?  Look at things we *have* proved to get an idea of which rules
# to apply?
#
# And we may need to teach it arithmetic, e.g. so that it can determine that
# 6 * 5 = 2 * 15.
#
# We could start with multiplication as repeated addition.  That would let us
# do the "multiplication in log(N) time by expressing one size in binary"
# thing that the ancient egyptians did.  But maybe that's a little too
# extreme.  Still, not sure how it would figure out he concept of e.g. prime
# number if multiplication is a black box.  For example, how would you know
# that the only things that divide into 5 are 1 and 5, if division is a black
# box?  But maybe we punt on that for now.


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

############
# Earliest exercises
#
# Apparently "Algebra 1: Concepts and Skills" is a recommended high school
# algebra textbook.  It can be found at
# www.mathacademicexcellence.com/Material_Algebra1.pdf .  It starts with
# substitution and simplification, e.g. "when y = 2, 10/y = 10/2 = 5" or "5 *
#  y == 5 * 2 == 10."
