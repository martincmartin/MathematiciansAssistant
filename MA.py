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
# A Google search confirms there's no theorem proving library for Sage, and no
# interface to call Coq.  I suppose I could always call into Coq from Sage?
# Recreating Coq in Sage would be fun, but seems like a lot of busy work,
# and wouldn't incorporate any improvements done to Coq.

import Parser

# from DeductionOrig import *
from Expression import Expression, CompositeExpression, var, forall

import DeductionApril2018

import sys

# import typeguard

from typing import Sequence

"""Next step: a little high school algebra.
It starts with two operators, + and *, and numbers (i.e. integers).
Those can always be "collapsed" down to a single number.  So, by themselves,
not very interesting."""

"""The next step is to add a single variable, say x.  Now what can you do?
If you have arbitrary expressions formed from num, x, + and *, you end up
with arbitrary polynomials of a single variable.  A good strategy to \
        understand them is to work only with first order polynomials, and see\
        how far you can go with those."""

"""So how do we get the system to understand that it could & should always 
collapse constant expressions?  e.g. that 2 + 3 should always (almost always?)
be collapsed to 5.

Because it simplifies later steps?  It's because of the goals we're trying to
achieve.  It's goal seeking behavior.

So what are the goals?  Maybe I should look at a good middle school algebra 
textbook.

One is simply solving equations.

Another is finding properties, e.g. x and y intercepts and slopes, 
etc.  Finding where two lines intersect.  Finding the area enclosed by 3 
lines (to start, one or two can be the x or y axes, or just vertical or 
horizontal lines.)

"Solve this equation" is different from "prove this statement."  When 
proving, you know the end statement.  When solving, you don't, although you 
know the form of the statement, e.g. x = ?, but you don't know the value on 
the RHS, that's the whole point.

Also solving systems of equations, e.g.
s + p = 48
p = 2*s

or

w = m + 5
w = 23

There are also rational numbers: adding them (common denominator), multiplying 
them (figuring out that you just multiply the numerators and denominators), 
dividing them (invert and multiply).

Let's start with solving equations of a single variable, e.g.

5 * x + 3 + 9 * x == x.

I think I'll need division for this.  Hmm.

This means "find the value(s) I can substitute into the expression to make it 
true."  Can we get it to figure out that changing it into the form "x == ?" 
makes that easy?  I don't see a way.  If it just starts with substituting 
arbitrary values, simplifying, and seeing if they're the same, there doesn't 
seem to be a way to go from that to trying to manipulate the original 
expression.  Maybe there is, if you recognize that solving "x == 23" is easy?
Because of the properties of ==, it's definition is basically "the two things on
either side have to be exactly the same."  So once you have a literal on one 
side, and a bare variable on the other, it's obvious what the set of 
solutions are, that's pretty much the definition of ==.

So, it could be phrased as "find the set of values that make this true,"
and initially, the only operator we have that gives us such a set is ==.  
Although we also need the idea of substituting and simplifying, since that's 
the very definition of what we're trying to do.

The substitution & checking truth value really is fundamental.  In the end, 
you're asked "what value(s) of x make this true?"  And you understand that 
e.g. if x is 5, then 3 * x is 15, and 3 * x == 20 is false, so 5 "doesn't 
work".  In other words, in elementary school you're taught to add, subtract, 
multiply and divide numbers.  The algebra is the "inverse problem" of 
knowing the result you want, and determining one of the inputs to get you 
that result: "what number do I put into the elementary school process to get 
the desired output?"

So substitution is fundamental.  But we need to not just treat it as a black 
box, since then all we can do is substitute individual values.  Instead, 
we need to reason about it: Given a problem like 5 * x + 3 + 9 * x == x, 
what "tricks" can we pull to find solutions to x?

Wikipedia has an interesting discussion on the history of algebra:

https://en.wikipedia.org/wiki/History_of_algebra#Stages_of_algebra

It started as equations expressed as full sentences.  It also started as 
geometric.

Euler, in his algebra text of 1770, defined it as "The science which teaches 
how to determine unknown quantities by means of those that are known."

"a 'cut and paste' geometry probably developed by surveyors as they figured 
out ways to understand the division of land."

Another technique is to try to approximate the answer, then look for 
corrections to the approximation.  For example, in "STAGES IN THE HISTORY OF 
ALGEBRA WITH IMPLICATIONS FOR TEACHING" by Katz (
https://link.springer.com/article/10.1007%2Fs10649-006-9023-7), an early 
Babylonian tablet solves the problem: the length plus the width of a 
rectangle is 6 1/2, the area is 7 1/2.  Find the length and width.  They 
start by taking half the sum and squaring it, i.e. taking the average of the 
length and width, and making a square out of it, that's an approximation to 
the original rectangle.  The difference in area is ((length - width)/2)**2.  
They prove this through a diagram, which could be turned into algebra using 
distributive law.

Looks like they would see the distributive law as a geometric thing: whenever
they needed to use the fact (a + b)c = ac + bc, they would have a rectangle 
with side length a + b, and other side c, and draw a line to divide it into 
two smaller rectangles, with side lengths a & c vs b & c.

I wonder if there was an implicity dimensional analysis in all this: some 
quantities were distances, others were areas, and e.g. you'd never add a 
distance to an area.  Perhaps it was more than that, i.e. you'd start with 
some diagram and only do things that made sense, e.g. you wouldn't add a 
diagonal of a rectangle to its length, since what would be the use of that, 
even though they're two lengths?

The square root already exists in these descriptions, it's not considered part
of algebra (fair enough).

Perhaps square roots come from solving the simplest quadratic equation?  
Because of all problems where you're given the area of a rectangle, 
the subset where it's a square are the simplest?  Because there's only one 
value, rather than separate length and width, no extra conditions needed to 
define a useful problem, etc.

Maybe pythagorean triples are related?

English does have the word "square" separate from "rectangle" for example.

Anyway, we start with an equation.  We look at it as something that can be 
true or false for various values of the variable, i.e. as a function from 
numbers to {True, False}.  Then we transform it in ways that preserve the 
function, i.e. the set of solutions.  And, for now, we can say that the 
only "ground truth" rule we know is that "x == [literal]" tells us the answer.
That leaves substitution out of the picture, but it's a place to start.  It 
also won't even work for quadratics where there's more than one answer; not 
sure how we'll handle sqrt() and +-.

The difference between "prove this" and "solve this" leads to differences in 
the code.  In "prove this" we have a context with known true statements.  In 
"solve this," at least for the simple case of linear systems, we only have a 
set of equations that are equivalent to each other, i.e. that have the same 
set of solutions.

[How will we handle 0*x = 0?  I guess we punt for now?]

So, (a) we don't have logical symbols (except maybe for external "forall"); 
and, are all rules of the form "forall{a, b, ... z} f(a, b, ..., z) = 
g(a, b, ... z)" where we can substitute an expression that matches one with 
the other side?  That gets us the distributive law, and fun things like
0 * x == 0.  It doesn't get us division though.  How do we handle 5 * x = 10?
Multiply both sides of the equation by the same number / expression.  So, 
we can't just modify 
subexpressions on either side of the equals, in isolation.  We need things 
like multiplying both sides of the equation.  And once we have that, we need 
a way to say "a != 0".  Hmm.

"""

"""
In elementary school we learn how to add, subtract, multiply and divide.  
Then in middle school, we pose the inverse problem: 5 * x = 10, what is x?
5 * x + 3 + 9 * x == x, what is x?  Basically, given some composable 
elements, we wonder, what value do we need to get the desired result?  I 
suppose later, the unknown might not just be a number, but we might ask 
which pieces do we compose how?

There's a kind of curiosity, how do we combine the pieces?  What tricks can 
we pull?  They're goal oriented.  Maybe we have a list of goals we've wanted 
to solve, and things we've tried that haven't worked, and when we see 
something new, we might recognize it as potentially helpful for a given goal.
So in general there are multiple goals, not just a single one.

So what does a freshman middle schooler do when first presented with 5 * x = 
10?  It seems a bit opaque at first.  Maybe they recognize it right away, 
if they've had a lot of practice with multiplication, from their times 
tables.  (So, match against what you've already seen: solving problems 
forward gives you a database of possible solutions for inverse problems.)

And they can always guess-and-check, substituting possible values.

But you need to make the leap to dividing both sides by 5.

Dividing is really the key, the inverse of multiplication.  e.g. 3 * x = 2,
solution is 2 / 3.

So how do you get to the idea of performing arithmetic on both sides of the 
equation?  The expressions (lhs and rhs) represent numbers, and you can 
certainly perform operations on numbers.  "How can I turn 5 * x into x?  
Divide by 5.  But how can I do it in a way that preserves truth value of the 
expression?"  How do you come up with the idea of doing it to the rhs as well?

Perhaps it's just one of these things that comes as a premise.  Part of the 
definition of =.  Certainly, if a = b is true, then in the expression a / c, 
I can substitute b for a and get b / c.  That is, a = b => a / c = b / c.  
And in general, if expr1 = expr2, then in expr3 I can substitute expr2 for 
subexpression expr1, without changing the result.

Going backwards is harder though, m*a = m*b => a = b if m != 0.  That lets 
us do a*x = b => 1/a * a * x = 1/a * b => x = b/a.

We might want be able to reason about preserving falsehood as well as 
preserving truth, that is, it might work better to think about
a != b => m*a != m*b (for m != 0).  But for now, we can stick to the original
version.  (Because (P => Q) iff (~Q => ~P).)

How do we establish this?  Essentially it's saying that division is well 
defined for divisor not equal to zero.  In other words, given that x / m is 
well defined and x = y, we can derive that x / m = y / m.  Let x = m*a and y 
= m*b, and we get the desired result.  That every element other than zero has a
unique multiplicitive inverse is one of the field axioms, maybe leave it at 
that?

Yeah, in Spivak they start with the ordered field axioms, and in the Epilogue
have a whole construction of reals out of rationals, then prove it for that 
specific construction.  So I think proving it is too hard.  I'm not sure what
they do in elementary school or middle school, they probably don't 
distinguish between rationals and reals a lot.

In fact, he says to ignore the construction; reals are a complete ordered 
field.  The construction just establishes there is such a thing as a complete
ordered field, and lets us prove that it is unique up to isomorphism.  Then 
he says to forget the construction and just use the properties.  So I think 
we can do something similar, start with the ordered field properties, 
and maybe say nth roots exist for all n or something similar.  Ordered is 
what allows you to say a + a = b + b => a = b (because 1 + 1 != 0.)  Just did
some Wikipedia searching.  The only axiom I could find to distinguish reals 
from rationals is completeness, i.e. any non-empty subset that's bounded 
above has a least upper bound.  And reals aren't first order axiomizable, 
so whatever alternate we might choose, it will need to generalize over sets 
or properties.  So l.u.b. is as reasonable as anything, and gets at the 
intuition that e.g. if we can bound sqrt(2) above and below, it must exist.

Actually, it turns out completeness is equivalent to the intermediate value 
theorm, and that might be a more practical expression, e.g. above where I 
talk about bounding sqrt(2), presumably with 1^2 = 1 and 2^2 = 4.  You still 
need to establish continuity, but that's true in general, e.g. x / sqrt(x^2) 
is sign(x), so -1 for negative x, +1 for positive x, but undefined for zero, 
and of course doesn't take on the value 1/2 anywhere.

So back to the question: given 5 * x = 10, how do you find x?  Where does the
idea to divide both sides of the equation come from?  Thinking about how to 
get x alone, i.e. get rid of the 5 *?  And the substitution principal of 
equality?

"""

"""
Quote from 'An Introduction To The History Of Mathematics' 6th ed by Hower Eves:
Chapter 2 section 1 p. 39
"    It should be noted, however, that in all ancient Oriental mathematics 
one cannont find even a single instance of what we today call a 
demonstration.  In place of an argument, there is merely a description of a 
process.  One is instructed, "Do thus and so."  Moreover, except possibly for a
few specimens, these instructions are not even given in the form of general 
rules, but are simply applied to a sequences of specific cases.  Thus, 
if the solution of quadratic equations is to be explained, we do not find a 
derivation of the process used, nor do we find the process described in 
general terms; instead we are offered a large number of specific quadratics, 
and we are told step by step how to solve each of these specific instances.  
It was expected that from a sufficient number of specific examples, 
the general process would become clear.  Unsatisfactory as the 
"do-thus-and-so" procedure may seem to us, it should not seem strange, 
for it is the procedure we must frequently use in teaching portions of 
grade-school and high-school mathematics."
"""


def ex(st: str) -> Expression:
    return Parser.parse(st)


def doit() -> None:
    # Helpful for testing / debugging.  I should remove this at some point.
    a = var("a")
    b = var("b")
    c = var("c")
    d = var("d")

    p = var("p")
    q = var("q")
    r = var("r")
    s = var("s")

    x = var("x")
    y = var("y")
    z = var("z")

    # Problem 0.1.2 from Dummit and Foote "Abstract Algebra."
    # M = (1  1; 0 1) (zero in lower left)
    A = var("A")
    M = var("M")
    B = var("B")
    P = var("P")
    Q = var("Q")
    R = var("R")

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
        proof = DeductionApril2018.try_rules(
            context, goal, general_rules, verbosity
        )

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

    rules = [
        defB, left_dist, right_dist, mult_associative
    ]  # , equals_reflexive]

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
    # "Let A bet the set of 2 x 2 matrices with real number entries."
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

    def helper_0_1_1(defX):
        print("!!!!! " + str(defX))
        helper(
            context=[defB, defM, defX],
            goal=ex("X in B"),
            general_rules=general_rules + [mat_mult] + ident_and_zero,
            verbosity=10,
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

    # helper_0_1_1(ex('X == [1 1; 0 1]'))

    helper_0_1_1(ex("X == [1 1; 1 1]"))
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
