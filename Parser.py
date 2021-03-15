from Expression import *
from tokenize import *
from typing import *
import io
import token


# Look!  A yak!  I think I'll shave it...


class Parser:
    type: Union[int, str]
    token: TokenInfo
    tokens: List[TokenInfo]

    keywords = {"in", "and", "or", "not", "==>", "<==>", "forall", "exists"}

    class_map = {
        STAR: Multiply,
        SLASH: Divide,
        PLUS: Sum,
        MINUS: Difference,
        LESS: Equal,  # TODO
        GREATER: Equal,  # TODO
        EQEQUAL: Equal,
        NOTEQUAL: Equal,  # TODO
        LESSEQUAL: Equal,  # TODO
        GREATEREQUAL: Equal,  # TODO
        "in": Element,
        "and": And,
        "or": Or,
        "not": Not,
        "==>": Implies,
        "<==>": Equivalent,
        "forall": ForAll,
        "exists": Exists,
    }

    def __init__(self, input_str: str) -> None:
        self.type = None
        self.token = None

        # We want to peek ahead, and all our input strings should be small
        # anyway, so just turn the generator into a list.
        tokens = list(tokenize(io.BytesIO(input_str.encode("utf-8")).readline))
        # print('**'+repr(tokens)+'**')
        self.tokens = []
        skip = 0
        for index, tok in enumerate(tokens):
            if tok.exact_type == ENCODING or tok.exact_type == NEWLINE:
                continue

            if skip > 0:
                skip -= 1
                continue

            # This is a hack because we're using Python's lexer, and Python
            # doesn't have ==> or <==>, but it does parse those into a sequence
            # of tokens.  We should really write our own lexer, wouldn't be
            # hard.
            if (
                tok.exact_type == EQEQUAL
                and index + 1 < len(tokens)
                and tokens[index + 1].exact_type == GREATER
            ):
                # Create a single ==> token.
                self.tokens.append(
                    type(tok)(
                        type=NAME, string="==>", start=None, end=None, line=None
                    )
                )
                skip = 1
            elif tok.exact_type == LESSEQUAL and index + 2 < len(
                tokens
            ) and tokens[
                index + 1
            ].exact_type == EQUAL and tokens[
                index + 2
            ].exact_type == GREATER:
                # Create a single <==> token.
                self.tokens.append(
                    type(tok)(
                        type=NAME,
                        string="<==>",
                        start=None,
                        end=None,
                        line=None,
                    )
                )
                skip = 2

            else:
                self.tokens.append(tok)

    def accept(self, *exact_types: Union[int, str]) -> bool:
        tok = self.tokens[0]
        for exact_type in exact_types:
            # Keywords (even Python keywords) end up as NAME types,
            # i.e. identifiers.  But here we want to treat them special.
            if isinstance(exact_type, str):
                assert exact_type in self.keywords
                pop = tok.string == exact_type
            elif exact_type == NAME:
                pop = tok.exact_type == NAME and tok.string not in self.keywords
            else:
                pop = tok.exact_type == exact_type

            if pop:
                self.token = self.tokens.pop(0)
                self.type = exact_type
                return True
        return False

    def expect(self, exact_type: Union[str, int]) -> None:
        tok = self.tokens.pop(0)
        if tok.exact_type != exact_type:
            if not isinstance(exact_type, str):  # pragma: no cover
                exact_type = token.tok_name[exact_type]
            raise SyntaxError("Expected %s but got %r" % (exact_type, tok))

    def atom(self) -> Expression:
        if self.accept(LPAR):
            e = self.expression()
            self.expect(RPAR)
            return e
        if self.accept(NAME):
            return var(self.token.string, None)

        """
        This is the Python syntax for list literals: [a, b, c].
        if self.accept(LSQB):
            mylist = [self.expression()]
            while self.accept(COMMA):
                mylist.append(self.expression())
            self.expect(RSQB)
            return CompositeExpression([List_()] + mylist)
        """

        # Matlab syntax for matricies: [a b; c d]
        if self.accept(LSQB):
            matrix: List[CompositeExpression] = []
            row: List[Expression] = []
            while True:
                row.append(self.expression())
                if self.accept(SEMI):
                    matrix.append(list_literal(*row))
                    row = []
                if self.accept(RSQB):
                    matrix.append(list_literal(*row))
                    return matrix_literal(*matrix)

        if self.accept(NUMBER):
            return num(int(self.token.string))

        raise SyntaxError("Unexpected token: " + repr(self.tokens[0]))

    def multiplicative(self) -> Expression:
        e = self.atom()
        while self.accept(STAR, SLASH):
            clz = self.class_map[self.token.exact_type]
            e = CompositeExpression([clz(), e, self.atom()])
        return e

    def additive(self) -> Expression:
        e = self.multiplicative()
        while self.accept(PLUS, MINUS):
            clz = self.class_map[self.token.exact_type]
            e = CompositeExpression([clz(), e, self.multiplicative()])
        return e

    def comparison(self) -> Expression:
        e = self.additive()
        # Allow a < b < c.
        while self.accept(
            LESS, GREATER, EQEQUAL, NOTEQUAL, LESSEQUAL, GREATEREQUAL, "in"
        ):
            clz = self.class_map[self.type]
            e = CompositeExpression([clz(), e, self.additive()])
        return e

    def negation(self) -> Expression:
        if self.accept("not"):
            return CompositeExpression([Not(), self.comparison()])
        return self.comparison()

    def and_or(self) -> Expression:
        e = self.negation()
        while self.accept("and", "or"):
            clz = self.class_map[self.type]
            e = CompositeExpression([clz(), e, self.negation()])
        return e

    def implies_equiv(self) -> Expression:
        e = self.and_or()
        while self.accept("==>", "<==>"):
            clz = self.class_map[self.type]
            e = CompositeExpression([clz(), e, self.and_or()])
        return e

    def forall_exists(self) -> Expression:
        # To do this properly, we'd also need to parse lists, and I've
        # shaved far too much yak today.
        return self.implies_equiv()

    def expression(self) -> Expression:
        return self.forall_exists()

    def parse(self) -> Expression:
        e = self.expression()
        self.expect(ENDMARKER)
        return e


def parse(input_str: str) -> Expression:
    return Parser(input_str).parse()
