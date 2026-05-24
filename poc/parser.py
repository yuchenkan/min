"""Parser for the min language.

program  = (import | binding)*
import   = 'from' dotted_name 'import' names
binding  = name '=' expr
         | name '(' params ')' '=' expr
expr     = name '(' args ')'
         | name
         | INT
         | STRING
         | '{' binding* expr '}'
args     = (expr (',' expr)*)?
params   = (name (',' name)*)?
"""

import re


# === Tokens ===

TOKEN_RE = re.compile(r"""
    (\s+)                     |  # whitespace
    (\#[^\n]*)                |  # comment
    (from|import)             |  # keywords
    ([a-zA-Z_][a-zA-Z_0-9]*) |  # NAME
    ([0-9]+)                  |  # INT
    ("(?:[^"\\]|\\.)*")       |  # STRING
    ([(){}=,.\n])                # punctuation
""", re.VERBOSE)


def tokenize(source, filepath='<input>'):
    tokens = []
    pos = 0
    line = 1
    col_offset = 0
    while pos < len(source):
        m = TOKEN_RE.match(source, pos)
        if not m:
            col = pos - col_offset + 1
            raise SyntaxError(f'{filepath}:{line}:{col}: unexpected char: {source[pos]!r}')
        start = pos
        pos = m.end()
        col = start - col_offset + 1
        ws, comment, kw, name, num, string, punct = m.groups()
        if ws:
            last_nl = ws.rfind('\n')
            if last_nl >= 0:
                line += ws.count('\n')
                col_offset = start + last_nl + 1
            continue
        if comment:
            continue
        if kw:
            tokens.append(('KW', kw, line, col))
        elif name:
            tokens.append(('NAME', name, line, col))
        elif num:
            tokens.append(('INT', int(num), line, col))
        elif string:
            tokens.append(('STR', string[1:-1], line, col))
        elif punct:
            if punct == '\n':
                line += 1
                col_offset = pos
            else:
                tokens.append(('PUNCT', punct, line, col))
    tokens.append(('EOF', None, line, 1))
    return tokens


# === AST ===

class Import:
    def __init__(self, module, names, line, col):
        self.module = module
        self.names = names
        self.line = line
        self.col = col

class Bind:
    def __init__(self, name, params, body, line, col):
        self.name = name
        self.params = params  # [] for value binding
        self.body = body
        self.line = line
        self.col = col

class Call:
    def __init__(self, name, args, line, col):
        self.name = name
        self.args = args
        self.line = line
        self.col = col

class Ref:
    def __init__(self, name, line, col):
        self.name = name
        self.line = line
        self.col = col

class Lit:
    def __init__(self, value, line, col):
        self.value = value
        self.line = line
        self.col = col

class Block:
    def __init__(self, bindings, expr, line, col):
        self.bindings = bindings
        self.expr = expr
        self.line = line
        self.col = col


# === Parser ===

class Parser:
    def __init__(self, tokens, filepath='<input>'):
        self.tokens = tokens
        self.pos = 0
        self.filepath = filepath

    def peek(self):
        return self.tokens[self.pos]

    def advance(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect(self, typ, val=None):
        tok = self.advance()
        if tok[0] != typ or (val is not None and tok[1] != val):
            raise SyntaxError(
                f'{self.filepath}:{tok[2]}:{tok[3]}: expected {typ} {val!r}, got {tok[0]} {tok[1]!r}')
        return tok

    def error(self, msg):
        tok = self.peek()
        raise SyntaxError(f'{self.filepath}:{tok[2]}:{tok[3]}: {msg}')

    def parse_program(self):
        items = []
        while self.peek()[0] != 'EOF':
            if self.peek()[0] == 'KW' and self.peek()[1] == 'from':
                items.append(self.parse_import())
            elif self.peek()[0] == 'NAME':
                items.append(self.parse_binding())
            else:
                self.error(f'expected import or binding, got {self.peek()[1]!r}')
        return items

    def parse_import(self):
        tok = self.expect('KW', 'from')
        module = self.parse_dotted_name()
        self.expect('KW', 'import')
        names = [self.expect('NAME')[1]]
        while self.peek()[0] == 'PUNCT' and self.peek()[1] == ',':
            self.advance()
            names.append(self.expect('NAME')[1])
        return Import(module, names, tok[2], tok[3])

    def parse_dotted_name(self):
        parts = [self.expect('NAME')[1]]
        while self.peek()[0] == 'PUNCT' and self.peek()[1] == '.':
            self.advance()
            parts.append(self.expect('NAME')[1])
        return '.'.join(parts)

    def parse_binding(self):
        """Parse binding: name = expr | name(params) = expr"""
        name_tok = self.expect('NAME')
        name = name_tok[1]
        line = name_tok[2]
        col = name_tok[3]

        if self.peek()[1] == '(':
            # name(...) — could be function binding or call
            self.advance()
            items = self.parse_args_or_params()
            self.expect('PUNCT', ')')
            # Must be followed by '=' for a binding
            self.expect('PUNCT', '=')
            params = self._as_params(items, line, col)
            body = self.parse_expr()
            return Bind(name, params, body, line, col)
        else:
            # name = expr
            self.expect('PUNCT', '=')
            body = self.parse_expr()
            return Bind(name, [], body, line, col)

    def parse_expr(self):
        tok = self.peek()

        # Block: { binding* expr }
        if tok[1] == '{':
            return self.parse_block()

        # Int literal
        if tok[0] == 'INT':
            t = self.advance()
            return Lit(t[1], t[2], t[3])

        # String literal
        if tok[0] == 'STR':
            t = self.advance()
            return Lit(t[1], t[2], t[3])

        # Name — could be call or reference
        if tok[0] == 'NAME':
            name_tok = self.advance()
            name = name_tok[1]
            line = name_tok[2]
            col = name_tok[3]

            if self.peek()[1] == '(':
                self.advance()
                args = self.parse_args()
                self.expect('PUNCT', ')')
                return Call(name, args, line, col)

            return Ref(name, line, col)

        self.error(f'expected expression, got {tok[1]!r}')

    def parse_block(self):
        tok = self.expect('PUNCT', '{')
        bindings = []
        # Parse binding* expr: keep parsing bindings until we hit something
        # that isn't a binding (no '=' after name or name(...))
        while True:
            saved = self.pos
            if self.peek()[0] == 'NAME':
                name_tok = self.advance()
                if self.peek()[1] == '=':
                    # name = expr
                    self.advance()
                    body = self.parse_expr()
                    bindings.append(Bind(name_tok[1], [], body, name_tok[2], name_tok[3]))
                    continue
                elif self.peek()[1] == '(':
                    # name(...) — check if followed by ) =
                    saved2 = self.pos
                    self.advance()
                    items = self.parse_args_or_params()
                    self.expect('PUNCT', ')')
                    if self.peek()[1] == '=':
                        # function binding
                        self.advance()
                        params = self._as_params(items, name_tok[2], name_tok[3])
                        body = self.parse_expr()
                        bindings.append(Bind(name_tok[1], params, body, name_tok[2], name_tok[3]))
                        continue
                    else:
                        # Not a binding — backtrack and parse as expr
                        self.pos = saved
                        break
                else:
                    # Just a name ref — backtrack and parse as expr
                    self.pos = saved
                    break
            else:
                break

        expr = self.parse_expr()
        self.expect('PUNCT', '}')
        return Block(bindings, expr, tok[2], tok[3])

    def parse_args(self):
        args = []
        if self.peek()[1] == ')':
            return args
        args.append(self.parse_expr())
        while self.peek()[1] == ',':
            self.advance()
            args.append(self.parse_expr())
        return args

    def parse_args_or_params(self):
        """Parse contents of (...) — could be args (exprs) or params (names).
        Parse as exprs. Validate as params later if needed."""
        return self.parse_args()

    def _as_params(self, items, line, col):
        """Validate that parsed exprs are all bare names (for function params)."""
        params = []
        for item in items:
            if not isinstance(item, Ref):
                raise SyntaxError(
                    f'{self.filepath}:{line}:{col}: function parameter must be a name')
            params.append(item.name)
        return params


def parse(source, filepath='<input>'):
    tokens = tokenize(source, filepath)
    parser = Parser(tokens, filepath)
    return parser.parse_program()


# === Test ===

if __name__ == '__main__':
    import sys

    src = """
from core.axioms import Extensionality

x = 5
y = add(x, 1)
f(a, b) = add(a, b)

result = {
    p = In(z, a)
    q = Implies(p, p)
    ForallRight(s1, q, z)
}

test = if(eq(x, 0), x, mul(x, 2))
"""

    ast = parse(src, '<test>')
    for node in ast:
        if isinstance(node, Import):
            print(f'import {node.module}: {node.names}')
        elif isinstance(node, Bind):
            params = f'({", ".join(node.params)})' if node.params else ''
            print(f'bind {node.name}{params} = {type(node.body).__name__}')
