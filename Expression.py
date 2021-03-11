# Notes in google docs, "How do you discover / learn algebra?"

# Possible yak shaving tasks:
# - Implement more operators, including parsing & printing.
# - Implement integer literals, including parsing & printing.
# - DRY the parser, at least the Infix part.
# - Write tests for the "pragma: no cover" comments in this source file
#   (Expression.py), then remove the comments.
# - Convert to Coq's notation:
#   forall
#   -> (implies, although also has => for defining functions)
# - An iterator that allows looping over a list while we're appending to it.
# - Change try_rule*() to only take a single "context", the union of the current
#   context and context_rules, and partition based on is_rule.
# - Add more types.

# - Have unit (integration?) tests for the theorem prover.  Most general is that
#   each step is logically valid.  We'd need a better representation of the
#   proof though, a tree rather than a list.  More specific is that the proof is
#   minimal, or near minimal, or doesn't have any obviously unneeded steps, etc.

# Check out SymPy, although it doesn't seem to have symbolic logic.  And 
# maybe 'it forms the core of Sage?'

# **********  Python types for Sets  **********
#
# This is super confusing and keeps changing.
#
# tl;dr:
#
# from __future__ import annotations
#
# Use collections.abc.Set (for immutable) or
# collections.abc.MutableSet.  Note that if frozenset fails type checking
# when passed to a function expecting Set, you're probably using typing.Set
# instead of collections.abc.Set.  Don't do "from typing import *" anymore.
#
# Check out the second answer here:
# https://stackoverflow.com/questions/35907309/what-are-the-differences-between-set-frozenset-mutableset-and-abstractset-in-p
#
# Don't use:
# typing.AbstractSet (use collections.abc.Set instead.)
# typing.MutableSet (use collections.abc.MutableSet instead.)
# typing.Set (use builtins.set instead.)
# typing.FrozenSet (use builtins.frozenset instead.)
#

from __future__ import annotations

import abc
import builtins
from enum import Enum, unique
from functools import total_ordering

from typing import Union, cast
from collections.abc import Sequence, Set, Iterable, Hashable, Mapping, \
    Collection

NumberT = Union[float, int]


class ExpressionType(Enum):
    ANY = 1
    NUMBER_LITERAL = 2
    OBJECT = 3  # https://en.wikipedia.org/wiki/Mathematical_object
    PROPOSITION = 4


@total_ordering
@unique
class Precedence(Enum):
    # This is only used for pretty-printing, not parsing, but needs to be kept
    # in sync with parser in Parser.py.

    # We should only use the ordering of these, not the actual value, because
    # the values will change as we add more operators.
    FORALL_EXISTS = 1
    IMPLIES_EQUIV = 2
    AND_OR = 3
    NEGATION = 4
    COMPARISON = 5
    ADDITIVE = 6
    MULTIPLICATIVE = 7
    FUNCALL = 8
    ATOM = 9

    def __lt__(self, other):
        return self.value < other.value


class Expression(abc.ABC):
    # We should consider getting rid of __mul__ and __add__.  They're used in
    # unit tests of the parser, but would be easy to replace with functions.
    def __mul__(self, rhs: Expression) -> "CompositeExpression":
        return CompositeExpression([Multiply(), self, rhs])

    # "+" already means "concatenate" for lists.  But concatenating
    # argument lists seems much rarer than constructing expressions
    # using "+", especially in abstract algebra.
    def __add__(self, rhs: Expression) -> "CompositeExpression":
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

    @abc.abstractmethod
    def repr_and_precedence(self) -> tuple[str, Precedence]:
        raise NotImplementedError  # pragma: no cover

    def __repr__(self) -> str:
        return self.repr_and_precedence()[0]

    @abc.abstractmethod
    def type(self) -> ExpressionType:
        raise NotImplementedError  # pragma: nocover

    def free_variables(self, exclude: Set["Variable"]) -> \
            Set["Variable"]:
        """Returns the set of free variables in this (sub-)expression.

        Free variables are the ones that are *not* covered by an forall or
        exists.  Their value / semantics comes from outside the
        expression."""
        return frozenset()

    def bound_variables(self) -> Set[Variable]:
        """Returns the set of bound variables in this (sub-)expression.

        Bound variables are any variables that are quantified over, either at
        the root or in any subexpression of the root.  These are the set of
        variables that will shadow any value / semantics from outside this
        expression.

        A variable may be bound more than once, with a different type in
        different instances.  So we just return the Variable, rather than the
        types.  This function is only used to find variables that need to be
        renamed to avoid collision, we don't use the type anyway.
        """
        raise NotImplementedError  # pragma: no cover

    # NOTE: In f(x)(y), f(x) returns a function, which is then called with
    # argument y.  So, f(x), a CompositeExpression, appears as the first
    # child of another CompositeExpression.  So the _tree methods will be
    # called on CompositeExpressions in that case.
    def constructor_tree(self, args: Sequence["Expression"]):
        pass

    def repr_tree(self, args: Sequence['Expression']) -> tuple[str, Precedence]:
        return (
            repr(self) + "(" + ", ".join([repr(arg) for arg in args]) + ")",
            Precedence.FUNCALL,
        )

    def free_variables_tree(
            self, args: Sequence['Expression'], exclude: Set["Variable"]
    ) -> Set["Variable"]:
        raise NotImplementedError  # pragma: no cover

    def bound_variables_tree(self, args: Sequence['Expression']) -> \
            Set[Variable]:
        raise NotImplementedError  # pragma: no cover

    def get_variables_tree(
            self, other_dummies: Mapping[Variable, ExpressionType]
    ) -> Mapping[Variable, ExpressionType]:
        return {}  # pragma: no cover

    def declass(self):  # pragma: no cover
        return self


class Node(Expression, abc.ABC):
    # Mathematica calls this an Atom.  In Mathematica, Head of a node is
    # its type.  Seems non-orthogonal.

    # Only used by Prefix and Infix nodes, but we have a helper method here,
    # so instead of creating a new class just for "has precedence," we put it
    #  here.  Could also use a mix-in I suppose.
    _precedence: Precedence

    def repr_and_precedence(self) -> tuple[str, Precedence]:
        return repr(self), Precedence.ATOM

    # Currently, our parser can't generate these.
    def repr_tree(self, args: Sequence[Expression]) -> tuple[str, Precedence]:
        return (
            repr(self) + "(" + ", ".join([repr(arg) for arg in args]) + ")",
            Precedence.FUNCALL,
        )

    def free_variables_tree(
            self, args: Sequence[Expression], exclude: Set["Variable"]
    ) -> Set["Variable"]:
        return {
            variable
            for child in args
            for variable in child.free_variables(exclude)
        }

    def bound_variables(self) -> Set[Variable]:
        return frozenset()

    def bound_variables_tree(
            self, args: Sequence[Expression]
    ) -> Set[Variable]:
        return frozenset().union(*(child.bound_variables() for child in args))

    def __eq__(self, other) -> bool:
        return isinstance(self, type(other))

    def __hash__(self):
        return hash(type(self))

    # Handy utility function used by repr_tree in some children.
    def wrap(self, child_repr_and_precedence) -> str:
        rep, child_prec = child_repr_and_precedence
        return rep if child_prec > self._precedence else "(" + rep + ")"

    # If we really are an atom, our derived class needs to implement this.
    # If we're an operator, this shouldn't be called.
    # Python docs for NotImplementedError say this is how you're supposed to
    # un-define a method in a subclass that's defined in a superclass.
    __repr__ = None

    def declass(self) -> str:  # pragma: no cover
        return type(self).__name__


class Variable(Node):
    _name: str

    def __init__(self, name: str) -> None:
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    def __repr__(self) -> str:
        return self._name

    def __eq__(self, other) -> bool:
        return isinstance(other, Variable) and self._name == other._name

    def __hash__(self):
        return hash(self._name)

    def type(self):
        # TODO: these needs types, even when leaves of expressions, e.g. in
        # x + y, x and y are both math objects, not propositions, whereas in
        # p and q, they're both propositions, not math objects.
        return ExpressionType.ANY

    def declass(self):  # pragma: no cover
        return self._name

    def free_variables(self, exclude: Set["Variable"]) -> Set["Variable"]:
        if self in exclude:
            return set()
        else:
            return {self}


class CompositeExpression(Expression, tuple[Expression, ...], abc.ABC):
    # We need a shorter name for this.  Just "Composite"?  That
    # collides with the name for non-prime numbers.  "Internal"?
    # "Tree"?  "Cons"?  "Cells"?  "List"?  In Mathematica, a list is a
    # composite expression with head List.

    # Inheriting from tuple means we can't modify the arguments
    # in the constructor, e.g. to rename variables to avoid shadowing.  And
    # Expression gives us a different definition of __add__ and __mul__,
    # which mypy complains about.
    # So we should probably be using composition instead of
    # inheritance here.  Oh well.

    # See https://stackoverflow.com/questions/50317506
    def __new__(cls, iterable: Iterable[Expression]):
        return tuple.__new__(cls, iterable)

    def __init__(self, iterable: Iterable[Expression]) -> None:
        super().__init__()
        assert all(isinstance(it, Hashable) for it in iterable)
        children = list(iterable)
        assert len(children) > 0
        children[0].constructor_tree(children[1:])

    # I'm using inheritance instead of composition.  Oh well.
    def repr_and_precedence(self) -> tuple[str, Precedence]:
        assert len(self) > 0
        return self[0].repr_tree(self[1:])

    def type(self) -> ExpressionType:
        return self[0].type()

    # Call pprint.pprint() on result.
    def declass(self) -> list[Expression]:  # pragma: no cover
        """Intended for debugging, shows the structure of the tree, even for
        invalid trees.
        """
        return [e.declass() for e in self]

    def free_variables(self, exclude: Set[Variable]) -> Set[Variable]:
        return self[0].free_variables_tree(self[1:], exclude)

    # TODO: Have all missing methods forward to their first argument, so we
    # don't need the boilerplate here?
    def get_variables(self, other_dummies: Mapping[Variable, ExpressionType]
                      ) -> Mapping[Variable, ExpressionType]:
        """Only defined for Quantifiers, gets the variables quantified over."""
        return self[0].get_variables_tree(other_dummies)

    def constructor_tree(self, args: Sequence[Expression]) -> None:
        """Called from __init__, allows methods to reject the tree."""
        pass

    def bound_variables(self) -> Set[Variable]:
        return self[0].bound_variables_tree(self[1:])


# I disagree with Python's "ask forgiveness, not permission" ethos, at
# least for this sort of mathematical pattern matching code.
def has_head(expr: Expression, clz: type) -> bool:
    return isinstance(expr, CompositeExpression) and isinstance(expr[0], clz)


# Name relations after nouns or adjectives, not verbs: Equal, not Equals; Sum,
# not Add.


class Infix(Node):
    _name: str
    _name_with_spaces: str
    _precedence: Precedence
    _type: ExpressionType

    def __init__(self, name: str, precedence: Precedence,
                 typ: ExpressionType) -> None:
        assert isinstance(precedence, Precedence)
        self._name = name
        self._name_with_spaces = " " + name + " "
        self._precedence = precedence
        self._type = typ

    def repr_tree(self, args: Sequence[Expression]) -> tuple[str, Precedence]:
        return (
            self._name_with_spaces.join(
                [self.wrap(arg.repr_and_precedence()) for arg in args]
            ),
            self._precedence,
        )

    def type(self) -> ExpressionType:
        return self._type


class Prefix(Node):
    _name: str
    _name_with_space: str
    _precedence: Precedence
    _type: ExpressionType

    def __init__(self, name: str, precedence: Precedence,
                 typ: ExpressionType) -> None:
        assert isinstance(precedence, Precedence)
        self._name = name
        self._name_with_space = name + " "
        self._precedence = precedence
        self._type = typ

    def repr_tree(self, args: Sequence[Expression]) -> tuple[str, Precedence]:
        assert len(args) == 1
        return (
            self._name_with_space + self.wrap(args[0].repr_and_precedence()),
            self._precedence,
        )

    def type(self) -> ExpressionType:
        return self._type


class Multiply(Infix):
    def __init__(self):
        Infix.__init__(self, "*", Precedence.MULTIPLICATIVE,
                       ExpressionType.OBJECT)


class Divide(Infix):
    def __init__(self):  # pragma: no cover
        Infix.__init__(self, "/", Precedence.MULTIPLICATIVE,
                       ExpressionType.OBJECT)


class Sum(Infix):
    def __init__(self):
        Infix.__init__(self, "+", Precedence.ADDITIVE, ExpressionType.OBJECT)


class Difference(Infix):
    def __init__(self):  # pragma: no cover
        Infix.__init__(self, "-", Precedence.ADDITIVE, ExpressionType.OBJECT)


class Element(Infix):
    def __init__(self):
        Infix.__init__(self, r"\in", Precedence.COMPARISON,
                       ExpressionType.PROPOSITION)


class Equivalent(Infix):
    def __init__(self):
        Infix.__init__(self, "<==>", Precedence.IMPLIES_EQUIV,
                       ExpressionType.PROPOSITION)


class Implies(Infix):
    def __init__(self):
        Infix.__init__(self, "==>", Precedence.IMPLIES_EQUIV,
                       ExpressionType.PROPOSITION)


class And(Infix):
    def __init__(self):
        Infix.__init__(self, "and", Precedence.AND_OR,
                       ExpressionType.PROPOSITION)


class Or(Infix):
    def __init__(self):
        Infix.__init__(self, "or", Precedence.AND_OR,
                       ExpressionType.PROPOSITION)


class Not(Prefix):
    def __init__(self):
        Prefix.__init__(self, "not", Precedence.NEGATION,
                        ExpressionType.PROPOSITION)


class Equal(Infix):
    def __init__(self):
        Infix.__init__(self, "==", Precedence.COMPARISON,
                       ExpressionType.PROPOSITION)


class Quantifier(Node):
    # Until we have a real type system, we want CompositeExpression to
    # essentially be a function call, i.e. that the first child is the function,
    # and the other children are the arguments.  And for now, we want all
    # arguments to be of type "bool" (or proposition?) or "object",
    # i.e. whatever quantifiers quantify over.  Which is a long way to say:
    # when constructing a Quantifier, we don't want the list of arguments to
    # include the variables quantified over, because those aren't
    # subexpressions (of bool or object type).

    _variables_map: Mapping[Variable, ExpressionType]

    def __init__(self,
                 variables: Collection[tuple[Variable, ExpressionType]]):
        for variable in variables:
            assert isinstance(variable, tuple)

        # Variable names must be unique.
        assert len({variable for variable, typ in variables}) == len(variables)

        self._variables_map = dict(variables)

    def type(self) -> ExpressionType:
        return ExpressionType.PROPOSITION

    def get_variables_tree(
            self, other_dummies: Mapping[Variable, ExpressionType]
    ) -> Mapping[Variable, ExpressionType]:
        assert other_dummies.keys().isdisjoint(self._variables_map)
        return self._variables_map

    def free_variables_tree(
            self, args: Sequence[Expression], exclude: Set["Variable"]
    ) -> Set['Variable']:
        # If variable is already in `exclude`, it just shadows the outer one.
        # That's confusing, but not wrong.
        # "|" is union.
        exclude = exclude | self.get_variables_tree({}).keys()

        return {
            variable
            for child in args
            for variable in child.free_variables(exclude)
        }

    def bound_variables_tree(self, args: Sequence[Expression]) -> \
            Set[Variable]:
        # Union the variables we're quantifying over, with those from
        # subexpressions.
        return self._variables_map.keys() | {
            variable
            for child in args[1:]
            for variable in child.bound_variables()}

    def constructor_tree(self, args: Sequence[Expression]) -> None:
        assert args[0].bound_variables().isdisjoint(self._variables_map.keys())

    def __eq__(self, other: Quantifier) -> bool:
        return type(self) == type(other) and self._variables_map == \
               other._variables_map

    def __hash__(self):
        return hash((type(self), frozenset(self._variables_map.items())))


class ForAll(Quantifier):
    def __repr__(self):
        return r"\forall{" + ", ".join(str(variable) + ": " + str(typ.name)
                                       for variable, typ in
                                       self._variables_map.items()) \
               + "}"


class Exists(Quantifier):
    def __repr__(self):
        return r"\exists{" + ", ".join(str(variable) + ": " + str(typ.name)
                                       for variable, typ in
                                       self._variables_map.items()) + "}"


class ListLiteral(Node):
    def __init__(self):
        pass

    def repr_tree(self, args: Sequence[Expression]) -> tuple[str, Precedence]:
        return (
            "[" + ", ".join([repr(arg) for arg in args]) + "]",
            Precedence.FUNCALL,
        )

    def type(self) -> ExpressionType:
        return ExpressionType.OBJECT


class MatrixLiteral(Node):
    def __init__(self):
        pass

    def repr_tree(self, args: Sequence[Expression]) -> tuple[str, Precedence]:
        if all(has_head(arg, ListLiteral) for arg in args):
            return (
                "["
                + "; ".join(
                    "  ".join(
                        repr(cell)
                        for cell in cast(CompositeExpression, arg)[1:]
                    )
                    for arg in args
                )
                + "]",
                Precedence.FUNCALL,
            )
        else:
            return (
                "[" + ", ".join([repr(arg) for arg in args]) + "]",
                Precedence.FUNCALL,
            )

    def type(self) -> ExpressionType:
        return ExpressionType.OBJECT


class NumberLiteral(Node):
    _value: NumberT

    def __init__(self, value):
        self._value = value

    def __repr__(self):
        return repr(self._value)

    def __eq__(self, other):
        return isinstance(other, NumberLiteral) and self._value == other._value

    def __hash__(self):
        return hash(self._value)

    def type(self) -> ExpressionType:
        return ExpressionType.NUMBER_LITERAL

    def declass(self):  # pragma: no cover
        return self._value


def makefn(clz: builtins.type[Node], name=""):
    def maker(*args):
        return CompositeExpression([clz()] + list(args))

    maker.__name__ = name if name else clz.__name__.lower()
    return maker


# You can use these handy functions to construct nodes, or the Parser below.
multiply = makefn(Multiply)
sum_ = makefn(Sum)
equal = makefn(Equal)
implies = makefn(Implies)
equivalent = makefn(Equivalent)
element = makefn(Element)
and_ = makefn(And, "and_")
or_ = makefn(Or, "or_")
not_ = makefn(Not, "not_")
list_literal = makefn(ListLiteral, "list_literal")
matrix_literal = makefn(MatrixLiteral)


def var(name: str) -> Variable:
    return Variable(name)


def iff(left, right):
    return equivalent(left, right)


def in_(left, right):
    return element(left, right)


def num(value: NumberT) -> NumberLiteral:
    return NumberLiteral(value)


def forall(variables: Iterable[tuple[Variable, ExpressionType]] |
           Iterable[Variable] | Variable,
           expr: Expression) \
        -> CompositeExpression:
    if isinstance(variables, Variable):
        variables = [(variables, ExpressionType.ANY)]
    elif all(isinstance(variable, Variable) for variable in variables):
        variables = [(variable, ExpressionType.ANY) for variable in variables]
    return CompositeExpression([ForAll(variables), expr])


def exists(variables: Iterable[tuple[Variable, ExpressionType]] |
           Iterable[Variable] | Variable,
           expr: Expression) \
        -> CompositeExpression:
    if isinstance(variables, Variable):
        variables = [(variables, ExpressionType.ANY)]
    elif all(isinstance(variable, Variable) for variable in variables):
        variables = [(variable, ExpressionType.ANY) for variable in variables]
    return CompositeExpression([Exists(variables), expr])
