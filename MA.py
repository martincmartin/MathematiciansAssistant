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
from Expression import Expression, CompositeExpression, var, forall, ExpressionType

# Save some typing
OBJECT = ExpressionType.OBJECT


import DeductionApril2018

import sys

# import typeguard

from typing import Sequence

"""Next step: a little high school algebra.
It starts with two operators, + and *, and numbers (i.e. integers).
Those can always be "collapsed" down to a single number.  So, by themselves,
not very interesting.

The next step is to add a single variable, say x.  Now what can you do?
If you have arbitrary expressions formed from num, x, + and *, you end up
with arbitrary polynomials of a single variable.  A good strategy to 
understand them is to work only with first order polynomials, and see how far
you can go with those.

So how do we get the system to understand that it could & should always 
collapse constant expressions?  e.g. that 2 + 3 should always (almost always?)
be collapsed to 5.

Because it simplifies later steps?  It's because of the goals we're trying to
achieve.  It's goal seeking behavior.

So what are the goals?  Maybe I should look at a good middle school algebra 
textbook.

One goal is simply solving equations.

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
expression. [Note that it could be looking at properties of what it sees, 
e.g. that when when x goes up, the LHS goes up.  Even look for patterns in 
how much it goes up, e.g. every time we increase x by one, how much does the 
LHS go up?]  Maybe there is, if you recognize that solving "x == 23" is easy?
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
rectangle is 6 1/2, the area is 7 1/2.  Find the length and width.  This is 
solving a quadratic equation. They 
start by taking half the sum and squaring it, i.e. taking the average of the 
length and width, and making a square out of it, that's an approximation to 
the original rectangle.  The difference in area is ((length - width)/2)**2.  
They prove this through a diagram, which could be turned into algebra using 
distributive law.

Looks like they would see the distributive law as a geometric thing: whenever
they needed to use the fact (a + b)c = ac + bc, they would have a rectangle 
with side length a + b, and other side c, and draw a line to divide it into 
two smaller rectangles, with side lengths a & c vs b & c.

I wonder if there was an implicitly dimensional analysis in all this: some 
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
Random aside: we to be able to prove things are equal, but also that things 
are not equal.  It needs an understanding that 5 != 6, and in general that 
the integers are all distinct, i.e. that integers with different 
representations and not equal.
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
theorem, and that might be a more practical expression, e.g. above where I 
talk about bounding sqrt(2), presumably with 1^2 = 1 and 2^2 = 4.  You still 
need to establish continuity, but that's true in general, e.g. x / sqrt(x^2) 
is sign(x), so -1 for negative x, +1 for positive x, but undefined for zero, 
and of course doesn't take on the value 1/2 anywhere.  According to 
Wikipedia, mathematicians used intuitive notions of continuity until the 18th 
century.  You can define it as lim{x -> c} f(x) = f(c), or the epsilon delta 
definition.  You can also define it as "lack of discontinuities," where 
discontinuity is a small (even infinitiesimal) change of input produces a 
finite (non-zero) change in the output.  Maybe that's equivalent to the epsilon 
delta definition.

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

"""
How mathematics got started:

We can actually go back before algebra, to arithmetic.  Adding and 
subtracting are somewhat straight forward, but division, and even 
multiplication, are interesting.

It depends a lot on the representation.  Things start with a 1:1 
correspondence representation, e.g. when counting goats, make a mark for 
every goat.  When the number gets big, it's easier to group them, into groups of
5 or 10 or whatever.  So you give a symbol for e.g. 10, then 100 = 10 10s 
gets a different symbol, etc like roman numerals.  Babylonians had 
a base sixty representation.  There are some tweaks; subtractive numbers, 
like IV for 4 in roman numerals, Babylonians had something similar.

Egyptians would reduce answers to a sum of reciprocals, e.g. 2/5 would be 
expressed as a sum of terms of the form 1/n.  They made an exception for 2/3 
though.  They did this to make subsequent multiplication easier.

So the question for basic operations becomes: how do you manipulate these 
representations to give the representation of the answer?  Long division and 
long multiplication weren't developed until the 15th century.  The writing 
medium was expensive and scarce (e.g. cuniform tablets, papyrus, rag paper).
It was too valuable to be used in any quantity as mere scratch paper.  The 
abacus helped, addition and subtraction are done as today, with carry and 
borrow.  The abacus competed with a new system for 400 years until 1500, 
when the new system won out.  I think they used tables for multiplication, 
the book doesn't really say.

Merzbach and Boyer says "The fundamental arithmetic operation in Egypt was 
addition, and ... multiplication and addition were performed in Ahmes's day 
through sucessive doubling. ... For division, the duplication process is 
reversed, and the divisor ... is successively doubled."

Babylonians had multiplication and reciprocal tables, squares and cubes, 
even exponentials, presumably for compound interest.  Reciprocal reduces 
division to multiplication.

Geometry was an inspiration.
"""

"""
Summarized Chapter 1 of Eves' "An Introduction to the History of Mathematics."
"""

"""
So if we wanted to discover the "multiplication in binary" thing, how would 
we do that?

Just adding n to itself m times won't lead to that, I think.  e.g. computing
7 * 5 through the sequence 7, 14, 21, 28, 35; it doesn't really stand out 
that you can go from 14 right to 28.  Although I suppose 2 is twice 1, 
and 8 is twice 4, so that's an interesting observation?

Anyway, another path is to play around with different sums.  e.g. notice that
7 + 7 = 14, 7 + 7 + 7 + 7 = 28, and 14 + 14 = 28.

There's also noticing the principal behind it: When computing 7 + 7 + 7 + 7, 
and you just computed 7 + 7, you actually have 7 + 7 twice in the original 
question and you're adding them together.

One way is to "play around with numbers" and look for these patterns.  That 
is, try different multiplication problems, maybe you'll end up trying 4*7, 
2*7 and 2*14, and notice the connections.  That at least would suggest 
hypotheses.

It's interesting that Ancient peoples never thought explicitly abstractly, 
but always by example.  There was some sort of implicit general thinking, 
of course, e.g. noticing that you can replace 7 in the above example with an 
arbitrary number (but not 2 or 4!).

Once it notices that 7 + 7 = 14 can help, it needs some way of expressing a 
recipe (or algorithm or whatever you call it), and expressing the new 
algorithm that uses 14 to roughly half the number of additions.

It also needs some practical notion that order doesn't matter.  More than 
just the statement of associativity.  I guess that can come from playing too?
The idea that you can just think in terms of x + y + z without parens, 
then combine any adjacent pairs in any order you want?

So what's the next step here?  The "expressing an algorithm" is interesting.
In some ways, the existing expression already does that, e.g. (7 + 7) + (7 + 
7) + 7 implies an order of operations.  Is that all we need, or do we need 
more?  I guess we need to bind variables, i.e. let x = 7 + 7; x + x + 7.  Or 
allow a graph rather than a tree.

In a way this really comes down to associative law & temporary variables.  
But at the same time, it's not about the formal system way of thinking, 
where we always have an explicit order and are using the associative law to 
manipulate that order.  You do get a higher level understanding that you can 
have "subtotals" that you add to get the overall total, and you can put 
arbitrary subsets into the subtotals and it doesn't matter.  How do we get 
that?  One way: play with expressions where we add a bunch of terms, and see 
what you can do with the associative rule.  Notice that you can get to any 
set of valid brackets you want.  Maybe pick a cannonical expression, like
((x + y) + z) + w, then convince yourself you can always get to that.  Notice
some invariants: the number of terms doesn't change, neither does their order
or the operators (+).  We probably need to have the concept of set built in, 
as well as the concept of list, those seem fundamental.

I think my language is all expressions, I don't think I have statements / 
sequences of deductions.  Maybe need to add that.
"""

"""
Quotes.

(I really need to move all this text to a separate text file.  Oh well.)

The way to understand this subject is by example.  -- Gilbert Strang, Linear 
Algebra and its Applications, Section 1.3.

Same sentiment, perhaps better:

It is examples more than definitions that make ideas clear -- in mathematics 
as in life.  -- Gilbert Strang, Linear Algebra for Everyone, Section 1.3 p. 24.

Not a quote, exactly, but Thurston's "On proof and progress in mathematics" 
https://arxiv.org/abs/math/9404236 is a good discussion of what's not 
captured by proving theorems.  e.g. the list of how people think of the 
derivative, in section 2.  It would be good to capture some of these ways of 
thinking in MA.

"We should recognize that the humanly understandable and humanly checkable 
proofs that we actually do are what is most important to us, and that they 
are quite different from formal proofs."  From Thurston's "On proof and 
progress in mathematics."
"""

"""
So after all this, where are we?

We want to do high school algebra.  Start with linear equations of a single 
variable, get into quadratics pretty quickly.

Use the "complete ordered field" stuff.  Can start with ordered field at 
first, at least for linear equations.  Only need completeness when we get to 
quadratics.

So, we have field properties, we have multiplicative inverse if non-zero.

What do we need to know about integers?  Presumably, we can use 3 as a 
shortcut for 1+1+1.  Can we prove 1+1+1 != 1+1?  Yes, we can prove 0 < 1, 
and then n < n+1 for all n.  When n = 2, we get 2 < 3 which (by trichotomy) 
means 2 != 3.

Example problems:

Simplify 5^-1 * 10.  (Just give it a black box for inverting & multiplying 
constants?  Seems legit.)

True or false: 5 == 0. (Again, a black box, since to people, it comes from 
the representation?  Some day we could give the computer a representation, 
e.g. binary, of numbers for it to work with.  But for now, black box seems 
legit.)

Find all x such that:

7 + x == 10
5 * x == 10
3 * x == 2

5 * x + 3 + 9 * x == x

So what's the thought process here?  That division is the opposite of 
multiplication is a key part.

You know, substitute & check *could* help.  For example, in 5 * x == 10, 
you might notice that the LHS increases as x increases, i.e. it might be a 
monotonically increasing function, we might try to prove that.  This is a 
sZuseful thing to note in other cases of root finding.

So what would "substitute and check and look for patterns" look like?  For 
5 * x == 10, you could start by substituting "special" numbers like 0, 
1 & -1, then go on to others.  You might notice that the LHS changes but the 
RHS doesn't, or that the LHS goes up by 5 every time x goes up by one.

Some of this is that the problem is too simple: there are so many ways to 
approach it.  Could treat it as root finding; could start from complete 
ordered field axioms.

How do we solve 5 * x == 10 starting with complete ordered field?  Don't need
completeness.

- Multiply both sides on the left by 5^-1.
- Associative on LHS, followed by 5^-1 * 5 == 1, followed by 1 * x == x.
- On RHS ... how to simplify 5^-1 * 10?  Maybe we start with that problem.  :)
- To simplify 5^-1 * 10, maybe need to establish that (k*b)^-1 * (k*a) == 
b^-1 * a?  How the hell are you going to prove that without a lot of facility
with proofs?  I guess (k*b)^-1 = b^-1 * k^-1, which is straight forward from 
the definition, then associativity / commutativity.  Still.
- To simplify 5^-1 * 10, you need to factor 10 as 5 * something.  Which is 
pretty much division.  I think just give it a black box for evaluating that.

Can you get this far with a breadth first walk through field axioms?  forall{
a}(a != 0 => exists{b}(b * a == 1)).  You'd have to substitute 5 in for a.  
You'd also have to establish that 5 != 0.

A generalization of 5 * x == 10 is a * x == 10 or even a * x == b.  In that 
case, there's no simplifying to do, x == a^-1 * b is the answer.

So we get back to: given a question like "find all x such that P(x)," how does
MA start thinking about it?  Would be nice if root finding wasn't a 
primitive, that should be emergent somehow.

Perhaps we start with the pieces in our language & axioms?  We have 1st order
logic, quantifiers, + - * /, comparisons, == and !=.  We have "in", although 
I don't think we have much support for sets.  Types are propositions and 
numbers.  Then we have an "engine" for manipulating them, based on ==, 
==> and <==>, along with pattern matching.  So == really is special.

***** Digression where I realize that even knowing what form the answer 
should take is subjective.

To express a solution set, we have to say something like "x == 2 or x == -2."
Basically, we have expressions that act as predicates, so you have to give a 
predicate for the answer.  Well, a simpler one, since by definition, 
the original statement is a predicate for the solution set.

One problem is that "simple" is subjective, but here we're looking for 
something more objective.  Do we just specify that the answer must be a 
disjunction of "x == {constant}" statements?  Seems lame, but otherwise, 
the system needs to understand that x == 2 is somehow simpler & more direct, 
and is an answer, whereas 5 * x == 10 isn't.  Although again, it comes into 
"what can you substitute for x to make it true?"  So it really is about 
solution sets.

The thing is, we don't have a way to denote most numbers.  In fact, we can 
only denote countably many numbers, and there are uncountably many reals.  
sqrt(2) is really short form for "x >= 0 such that x * x == 2."  So what does
it mean to specify the solution set?  What about, say, a 5th degree 
polynomial, where we can only specify the answer in terms of various 
radicals?  Not to mention Pi.  How do we even define Pi, or e?  Spivak 
defines Pi as the area of the unit circle, calculated as twice the area of 
the unit semicircle, Pi = 2 * integrate(sqrt(1 - x^2), x = -1 .. 1).

Even in the simple case of the form (some literal) * x == (some other literal), 
the form of the answer isn't obvious.  You could reduce it to simplest terms.
Do you want a proper or improper fraction?  Sometimes you can get a whole 
number, sometimes you can't.  And none of that applies when you have 
constants (i.e. variables other than x) as the coefficients.  There's 
something analogous in a*b*x == c*b*x where you can cancel the b, but it's 
not exactly the same.

So then what does it mean to specify a solution set?  It seems to be 
something like a set of "expressions that's as simple as I can make it,"
where simple is somewhat subjective.  In fact, it's not just a list of 
numbers, as it can be an infinite set, e.g. all numbers between 3 and 5, 
or rational numbers, or a cantor set.  Hmm.

***** End digression

So, good to know.  For middle school algebra, we'll just say it's numbers of 
the form b^-1 * a.  In fact, we could start with it trying to simplify 
numbers of the form b^-1 * a to a whole number constant (or integer).  I wonder 
if it can prove that it can't.  Might need induction.  So skip that for now.

Ok.  So given 5 * x == 10, the idea is to find a number, in the form b^-1 * 
a, that we can substitute in for x.

Adding the RHS as a goal and manipulating the LHS doesn't really work.  We 
want to multiply both sides of the equation by 5^-1.  How should that work in
MA?  How does it work in e.g. Coq?  In Software Foundations, at least, 
I think Coq is always proving true statements, it never has "find all X that 
make this proposition true."  Plus, Coq is only worried about proving 
statements, not figuring them out, so substituting in the correct value works
for it.

Coq has a PeanoNat.Nat.mul_cancel_r theorem:
forall n m p : nat, p <> 0 -> n * p = m * p <-> n = m

The proof of that (in coq-8.13.0/theories/Numbers/NatInt/NZMulOrder.v) is 
not how you'd explain it to a middle schooler.

But it's straight forward to prove I guess, at least in our case with the 
field axioms.  First you prove the "easy" direction, n = m -> n * p = m * p.
That's just intros, rewrite and reflexivity.  Then use that to multiply by p^-1.  
"""

"""
Do we start with properties of numbers (literals)?  e.g. 6 = 2 * 3, 6 / 3 = 
2?  Do we start with how to simplify fractions, e.g. 12/6 and 6/12?

On the one hand, I don't want to specify the exact form of an acceptable 
answer; that's cheating.  The system should figure out how much it can 
simplify things, and in general, how useful it can make the answer.  On the 
other hand, it needs problems to solve in order to guide it, in order for it 
to understand what's useful and what isn't.  Where do those problems come 
from, and how are they specified?

Some problems come from outside, e.g. ancient Egyptian mathematicians having 
to figure out how much tax people pay, or how much their land was eroded when
the Nile flooded.  Or figuring out astronomical things like the calendar or 
plant conjunctions or whatever.  But some comes from "playing" with the 
subject, a kind of "hey look what I can do!"  How is the playing motivated?  
At least part of that needs to come externally.  Things like "find a 
representation that uses the fewest symbols" works in simple cases, but as 
things grow it will quickly miss the point.

It's reasonable for external requirements, say the tax collector, to say the 
result needs to be specified in a known form, e.g. as a mixed number (whole 
number plus proper fraction.)

Perhaps we can even start with ways of simplifying things like 12/6.  The 
idea being it comes up with the concept of factoring, i.e. writing 12 = 2*6, 
rather than the other ways you can write 12 that aren't helpful, 
e.g. 5+3+2+2.  Basically, the external entity lists a required form, but all 
mathematical understanding, including factoring etc, is developed by MA.

So how does it develop the idea that 12/6 can be simplified, where 2/3 can't?
Perhaps it plays with division of small integers.  Does it do this with 
division as a black box, or as the inverse of multiplication?  Division can 
be thought of as "how many times is one number contained within another?"  Or
do we start with Euclidean division, where the result is a whole number with 
remainder?  Think of 20 / 5 as "the number of 5s that must be added to give 
20"?  There's a concept of creating groups of size 5; you get 4 such groups.

"Division involves thinking about a whole in terms of its parts." from the 
Wikipedia on "Quotition and partition."   Do we see it as a kind of repeated 
subtraction?  How many times can you subtract 5 from 20?  Yeah, apparently 
that's the only way Euclid could do it, and describes it in Elements.  Strange.

This doesn't make the connection to multiplication obvious, but maybe that's 
ok.  It's a long way from field axioms though, and being useful for 5*x == 
10.  But maybe this is the right / natural way to think of it in terms of 
number literals?  It's using an algorithm, and applying it to examples, 
to understand its properties.

So what, exactly, are we trying to find?  That 12 can be factored as 2*6, 
but 13 can't be factored?  13/6 can be computed / simplified to 2 and 1/6, 
or 2 remainder 1.

Maybe start with addition/subtraction instead of multiplication/division, 
e.g. solve x + 7 == 11.

How do I solve that?  I memorize the 9 pairs that add to 10, so I know that
3 + 7 == 10.  But we need one more than 10, so the answer is one more than 3,
i.e. 4.  How do we get from there to subtraction?  One way is to think of 
this operation -- something + 7 == 11 -- as an operation on it's own, 
it takes in 11 and 7 and returns 4.  And of course, that's subtraction.  So 
essentially, "solve x + a == b" is considered a primitive, and we use that as
the definition of subtraction.

Group Axioms:

a + b exists and is a number (Closure)
(a + b) + c == a + (b + c) (Associativity)
0 + a == a + 0 == a (Identity)
-a + a == a + -a == 0 (Inverse)

But let's go with the field (or group) angle, where we have an axiom about an
additive inverse.  I think we can have an explicit goal to put the equation 
in a "x == ??" form, where the RHS doesn't have an x.  So we look at the RHS 
and think "hey that's great, no x there!"  Then we look at the LHS and see "x +
7".  And we think "ok, how do we get rid of the + 7?"  And we notice, 
there are two rules to get rid of +, one is a + 0 = a, the other is a + -a = 
0.  So ... then what?  Adding anything to the LHS will temporarilty increase 
the number of +s.  Maybe we try to turn the 7 into a zero, so we can apply 
the x + 0 == x rule?  Essentially, we're working backward from the goal, 
thinking "what's the step before having just "x" on the LHS?"  And that has 
to be the "x + 0" rule, since that's the only rule with a single symbol on 
one side.  (My current system that simply applies all rules would find this.)
Then the question is: where does the zero come from?  That's when we think of
using the a + -a rule.

So the trick is to figure out what value to use for a, and get the idea of 
applying it to both sides of the equation.

This is very different from what happened historically.  Historically, 
there were no negative numbers aka additive inverse.  Instead, subtraction 
was seen as taking things away.  The work was essentially in a unary 
representation; having groups for 10, 100, etc. can be mostly thought of as 
an optimization.  For example, Euclid described division as repeated 
subtraction, and the representation for numbers at the time didn't make long 
division practical.

So we can try to work backwards from the goal for the LHS of just x, and find
that x + 0 or 0 + x must be the penultimate step since there's only one rule in 
the  group axioms that will get just x.  That's already brute force, but maybe 
that's ok.  But how do we turn the 7 into zero, i.e. how do we go from x + 7 
to x + 0?  Looking at rules that can produce 0 where there was none, 
i.e. looking at rules that change the number of zeros, we have that exact 
same rule, a + 0 == 0, and rule about inverses, a + -a == 0.  Of course, 
we can apply the identity rule to the premise to provide our single zero in 
lots of places, but that's not useful.  So it's more useful to focus on 
getting rid of 7, rather than introducing zeros.

That's an insight we'd like MA to make: having goals based on the AST, 
like introducing zero and eliminating 7, and discovering that "eliminate 7" 
is more fruitful than "introduce 0."

So we have x + 7, and we'd like to get to just x.  No rule will do that
right away, since 7 != 0.  So working backwards, we need either 0 + x or x + 
0.  Working forwards, we need to get rid of the 7.  Associativity does not 
change any numbers.  Identity only gets rid of 0, and 7 != 0.  So we need to 
use inverse.

There's kind of another rule though, the black box + rule, e.g. I can turn 7 
into any other number by adding something to both sides of the equation.  How
does it realize that's not the way to go?  I feel like we need some simple 
notion of edit distance.  Should it be purely from the AST geometry, 
e.g. number of substitutions/additions/subtractions of nodes to get us what 
we want?  Or should it somehow depend on the group axioms?  Maybe start with 
the pure geometry edit distance, and MA can learn to generalize it?  Maybe MA
comes up with an edit distance based on the rules?  e.g. a zero literal is 
special, because axioms mention it.  Hmm.

Dragon Box Algebra (a) starts with the explicit goal of getting x (the dragon
box) alone on one side, and (b) the very first level is x + 0 + 0.  So this 
is a good point that I had overlooked: we could start with x + 0 + 0 == 5 and
ask, what is x?

I also think it's ok to start with a simple edit distance metric, as long as 
the system can create new, better metrics from it, based more on what the 
rules allow.

Part of the answer is having the system come up with higher level 
descriptions of what it can solve, e.g. realizing that any subexpression that
doesn't contain x is just a constant, and the kinds of expressions it can 
simplify, etc.

So what does it learn from x + 0 + 0?  That x + 0 is solveable, i.e. that x + 0
is a good goal.  That's how it gets the idea to transform x + 7 into x + 0.

And of course, it recognizes that 0 is special in that way, but x is the 
"target variable" provided in the problem statement.  If given "x + 7 + -7 == 
11, what is x?" it should recognize that what's special here is that -7 is 
the additive inverse of 7, not a specific fact about 7 + -7.  i.e. that 
problems of the form x + a + -a can be solved by such as such steps.  So we 
do need a way to represent an algorithm, I think.

We could start with a simple A* search with a simple edit distance as the 
metric, at least to get unblocked.  But the long term goal is for the system 
to create its own metrics, based on problems it realizes it knows how to solve.

So what are the pieces we have?
- applying an axiom to a subexpression.
- when a premise is of the form a == b, we can transform that to f(a) == f(
b), for arbitrary f.  Well, maybe not?  e.g. if we have the premise x + 3 == 
7, we can add (x + 3) * 0 == 7 * 0.  But it doesn't follow that any solution 
to the latter is acceptable.  So how to interpret premises with free variables?

We certainly don't want to restrict transformations to "if and only if" ones.
i.e. we don't want all intermediate statements to have to be equivalent to 
the problem statement.  We want to be able to say "if x satisfies the goal, then
P(x)" without worrying about the inverse.

So I suppose we could add a premise, for the particular problem, that e.g.
x * x == 4.  This is a statement that's true about x in this problem, 
a way of defining a property on x or a solution set implicitly.  So another 
true statement is that x * x * 0 = 0, but that second statement isn't 
equivalent to the original, i.e. just because we find an x where that's true, it
doesn't mean it satisfies all conditions on x.  So these statements are 
necessary conditions, we also need ones that are sufficient.

Well, if you can prove a necessary condition of the form "x == ...", and the 
equation has at least 1 solution, then it only has a single solution and 
you've found it.  Still, would be nice for it to figure out that x + 5 == x + 10
has no solutions.

So fine, we add "x + 5 == 11" as a premise (just for this problem), 
and x becomes a constant like pi or e.  And the person creating the problem 
makes sure it's consistent.

So then we get back to, how does it find a path to the solution?  We give it 
x + 0 + 0, and it applies the additive identity twice, and it learns to like 
applying additive identity forward.  And does it have a notion of what kind 
of problems it can solve?  It has to get the idea that creating a zero is 
good, that's why it tries to apply the additive inverse.  Otherwise, 
converting x + 7 into x + 0 doesn't seem to have improved anything; edit 
distance wise, they're both the same distance from x (need to remove one leaf
and one operator).

The set of things it knows how to solve are essentially "anything with a 
single x, and any number of + and 0."  Of course, the language to express 
these predicates is a whole other can of worms.  We could use something black
box like modern ML.  Or we could create a simple language to start with, 
i.e. just provide some features, like some kind of pattern matching.  Later 
could have something more advanced like a generalization of regular 
expressions.  I mean, before long we'll need something that can recognize all
the variants from associativity and commutativity are the same.  I suppose 
that's easy to express in a symbol symbolic level: order and shape of tree 
doesn't matter, all that matters is that the operators are all +, and we can 
put the leaves in any order.

There's also the concept of simplifying, the idea that 8 is basically always 
better than 3 + 5, so whenever you see a sum of literals, you should just do 
the sum.  In other words, it doesn't matter what your goal is, before even 
considering your goal, just do these transformations because they're better 
for everything.

So, it starts with the idea that it wants to get to just "x" in one step.  Of
course it can't.  But after solving x + 0, it realizes anything of that form 
it can solve.  For now, punt on the whole representation for trees that can 
be solved, and just have features about what it's composed of, i.e. "bag of 
operators" and "bag of leaves" I guess.

The problem of how to represent the set of things you can solve is one of 
these big, "grand challenge" type problems that I'm not going to solve now.  
So, we can just put something simple in and come back to it later.

So where am I?  I need the concept of "forms I can solve," that starts with
x == (no x), and expands over time.  Then we've given the problem x + 0 + 0 
== 7, and we think "the RHS is already of the appropriate form, how do I get 
the LHS to be just x?"  And we can use edit distance, and we'll notice that (
a) we want to reduce the number of zeros, and (b) the number of +s, and that 
additive identity does that for us.

In fact, dragon box starts with just an expression, not an equation, and the 
goal of reducing it to just "x".  It then has expressions of the form "x + 7 
+ -7".

It turns out, tree edit distance is not straight forward to compute; there 
are a couple solutions, Zhang & Shasha have a paper from 1989, 
see implementations here:
 
https://zhang-shasha.readthedocs.io/en/latest/
https://github.com/timtadh/zhang-shasha

another called APTED seems to be an improvement:

https://pypi.org/project/apted/

Actually, tree edit distance isn't quite what I want, because I don't have a 
single target tree.  Instead, I have a class of trees that I know how to 
solve, and I want to know what I have to change to get into that class.  Hmm.

And so the reasonable way to compute the distance depends on the 
representation of "solvable expressions."  For example, if it's a bag of 
leaves and operators, we just look at leaves or operators not in the bag.  So
let's just do that.

"""


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
        (P, Q, R),
        ex("(P * Q) * R == P * (Q * R)")
    )

    # Multiplication distributes over addition
    left_dist: CompositeExpression = forall(
        (P, Q, R),
        ex("R * (P + Q) == R * P + R * Q")
    )
    right_dist: CompositeExpression = forall(
        (P, Q, R),
        ex("(P + Q) * R == P * R + Q * R")
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

    def helper_0_1_1(defX):
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
    helper_0_1_1(ex('X == [1 1; 0 1]'))
    # This one is false, and we don't have a way yet to prove that things are
    # false.
    # helper_0_1_1(ex("X == [1 1; 1 1]"))

    # This one is true, since both sides evaluate to the zero matrix.  But we
    # can't discover this, because (a) we produce a ton of distracting crap,
    # and (b) we only ever work forward, never backward.
    helper_0_1_1(ex("X == [0 0; 0 0]"))
    sys.exit(0)
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
