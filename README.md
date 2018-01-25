# MathematiciansAssistant
Collaborative theorem discoverer.

Possible fonts for "x + y" logo:

Tex's default font is "Computer Modern."  https://en.wikipedia.org/wiki/Computer_Modern
Terminal fonts:
    Glass TTY VT220: http://sensi.org/~svo/glasstty/  http://sensi.org/%7Esvo/glasstty/Glass_TTY_VT220.ttf
    LCD Solid: http://www.fontspace.com/lcd-solid/lcd-solid
    


[ Is the name a problem?  Will physicists / enginners look at it and think its
too formal?  I can't think of a better name, and it does help with the
mathematical part of physics / engineering, not any other parts. ]

# About

Mathematician's Assistant will help help physicists, mathematicians and
engineers explore mathematical spaces and generate outlines of possible proofs:
a series of conjectures that each seem likely to be true, and if so would prove
the desired result.

Given some axioms or assumptions that define a space, it can also generate
examples of mathematical objects in that space and start to characterize the
space.

Mathematician's Assisant is not a proof assistant.  It doesn't ensure that each
step in its outlines are formally provable.  Instead, it is attempting the same
goal as the working mathematician, theoretical physicist or engineer.  It makes
educated guesses about the structure of a space or outline of a proof.  Of
course, the conjectures could be given to an existing automatic theorm prover or
proof assistant to fill in the details (if they are provable), or provide
feedback (if it proves them false.)

Perhaps the best way to think about Mathematician's Assistant is as automating
the Master's Thesis[1].  When a new technique or other mathematical space opens
up, there are often many problems that are worth exploring.  Mathematician's
Assistant can try straight forward steps on many of them, notice patterns in
examples that succeed or fail, generate hypotheses from those patterns, and set
out to prove or disprove the hypotheses (if that's easy), prove them in a
restricted domain, and / or provide evidence such as classes of examples for
which the technique works or doesn't.

It is not designed to work on its own or be used by someone who is not
knowledgeable in the field.  Rather, if the sorts of examples it generates are
too simple, or hypetheses it generates are obviosly wrong, a field expert will
need to step in and direct it, e.g. by defining a class of examples that are
considered too easy, and if convenient, providing a proof that they satisfy the
proposition.  MA could then learn from the proof, e.g. trying to generalize it,
or examining the steps that it deemed not worth pursuing and adding them as
training examples, to make it more likely to try them in the future.

[1] I am indebted to Ian Horswill for this description of a different project,
my Ph.D. thesis.

- Talk about the interplay between theorm proving and guessing / outlines: much
  like a working academic, when MA generates hypotheses, it then attempts to
  prove or disprove them.  It does this both because it can have certainty in
  what it has proved, but also so that it can learn from them, adjusting its
  internal weights / heuristics on what is likely to succeed and what isn't.

- So why do we use a theorm prover?  To generate examples we can learn from.  We
  can also use it to automatically prove the easier steps, of course.

- Using machine learning to learn properties of expressions that make
  them worth attempting Integration by parts.  Note that this is just
  "worth attempting."  It may not work, and there will be expressions
  that are attackable by integration by parts that the classifier will
  incorrectly say aren't worth trying.

- Some examples of rules / heuristics and how they combine to solve simple problems.

- Talk about the differences between mathematicians and physicists approaches to
  math: physicists are happy to be guided by physical intuition, e.g. assuming
  that everyting is analytic.  [I wish I could find that quote by Feynman about
  how people who are mathematicians don't do well at physics.  Is it because
  they get caught up in what's formally provable?  Oh well.]
  