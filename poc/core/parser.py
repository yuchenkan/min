"""Parser for the min language.

program  = (import | bind)*
import   = 'from' dotted_name 'import' names
bind     = '=' '(' name expr ')'
expr     = '\' '(' params ':' expr ')'
         | '[' (expr (',' expr)*)? ']'
         | '?' '(' expr ',' expr ',' expr ')'
         | '{' bind* expr '}'
         | expr '(' (expr (',' expr)*)? ')'
         | name
         | INT
         | STRING
params   = name*
"""


# === Tokens ===

KEYWORDS = {'from', 'import'}
PUNCTUATION = set('(){}[]=,.:?\\')
ESCAPES = {'\\': '\\', '"': '"', 'n': '\n', 't': '\t'}


def tokenize(source, filepath='<input>'):
    tokens = []
    pos = 0
    line = 1
    col_start = 0

    def err(msg):
        raise SyntaxError(f'{filepath}:{line}:{pos - col_start + 1}: {msg}')

    while pos < len(source):
        c = source[pos]

        if c in ' \t\r\n':
            if c == '\n':
                line += 1
                col_start = pos + 1
            pos += 1
            continue

        if c == '#':
            while pos < len(source) and source[pos] != '\n':
                pos += 1
            continue

        col = pos - col_start + 1

        if c == '"':
            pos += 1
            s = []
            while pos < len(source) and source[pos] != '"':
                if source[pos] == '\\':
                    pos += 1
                    if pos >= len(source):
                        err('unterminated string escape')
                    esc = ESCAPES.get(source[pos])
                    if esc is None:
                        err(f'invalid escape: \\{source[pos]}')
                    s.append(esc)
                else:
                    s.append(source[pos])
                pos += 1
            if pos >= len(source):
                err('unterminated string')
            pos += 1
            tokens.append(('STR', ''.join(s), line, col))
            continue

        if c.isalpha() or c == '_':
            start = pos
            while pos < len(source) and (source[pos].isalnum() or source[pos] == '_'):
                pos += 1
            word = source[start:pos]
            if word in KEYWORDS:
                tokens.append(('KW', word, line, col))
            else:
                tokens.append(('NAME', word, line, col))
            continue

        if c.isdigit():
            start = pos
            while pos < len(source) and source[pos].isdigit():
                pos += 1
            tokens.append(('INT', int(source[start:pos]), line, col))
            continue

        if c in PUNCTUATION:
            tokens.append(('PUNCT', c, line, col))
            pos += 1
            continue

        err(f'unexpected char: {c!r}')

    tokens.append(('EOF', None, line, 1))
    return tokens


# === AST ===

class Import:
    def __init__(self, module, names, line, col):
        self.module = module
        self.names = names
        self.line = line
        self.col = col
    def __repr__(self):
        return f'from {self.module} import {", ".join(self.names)}'

class Bind:
    def __init__(self, name, expr, line, col):
        self.name = name
        self.expr = expr
        self.line = line
        self.col = col
    def __repr__(self):
        return f'=({self.name} {self.expr})'

class Fn:
    def __init__(self, params, body, line, col):
        self.params = params
        self.body = body
        self.line = line
        self.col = col
    def __repr__(self):
        p = ' '.join(self.params)
        return f'\\({p} : {self.body})'

class Call:
    def __init__(self, callee, args, line, col):
        self.callee = callee
        self.args = args
        self.line = line
        self.col = col
    def __repr__(self):
        return f'{self.callee}({", ".join(repr(a) for a in self.args)})'

class Ref:
    def __init__(self, name, line, col):
        self.name = name
        self.line = line
        self.col = col
    def __repr__(self):
        return self.name

class Lit:
    def __init__(self, value, line, col):
        self.value = value
        self.line = line
        self.col = col
    def __repr__(self):
        if isinstance(self.value, str):
            return f'"{self.value}"'
        return str(self.value)

class List:
    def __init__(self, items, line, col):
        self.items = items
        self.line = line
        self.col = col
    def __repr__(self):
        return f'[{", ".join(repr(i) for i in self.items)}]'

class Block:
    def __init__(self, bindings, expr, line, col):
        self.bindings = bindings
        self.expr = expr
        self.line = line
        self.col = col
    def __repr__(self):
        parts = [repr(b) for b in self.bindings] + [repr(self.expr)]
        return '{ ' + ' '.join(parts) + ' }'

class If:
    def __init__(self, cond, then, else_, line, col):
        self.cond = cond
        self.then = then
        self.else_ = else_
        self.line = line
        self.col = col
    def __repr__(self):
        return f'?({self.cond}, {self.then}, {self.else_})'


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
            if self.peek()[1] == 'from':
                items.append(self.parse_import())
            elif self.peek()[1] == '=':
                items.append(self.parse_bind())
            else:
                self.error(f'expected import or bind, got {self.peek()[1]!r}')
        return items

    def parse_import(self):
        tok = self.expect('KW', 'from')
        module = self.parse_dotted_name()
        self.expect('KW', 'import')
        names = [self.expect('NAME')[1]]
        while self.peek()[1] == ',':
            self.advance()
            names.append(self.expect('NAME')[1])
        return Import(module, names, tok[2], tok[3])

    def parse_dotted_name(self):
        parts = [self.expect('NAME')[1]]
        while self.peek()[1] == '.':
            self.advance()
            parts.append(self.expect('NAME')[1])
        return '.'.join(parts)

    def parse_bind(self):
        tok = self.expect('PUNCT', '=')
        self.expect('PUNCT', '(')
        name = self.expect('NAME')[1]
        expr = self.parse_expr()
        self.expect('PUNCT', ')')
        return Bind(name, expr, tok[2], tok[3])

    def parse_expr(self):
        tok = self.peek()

        if tok[1] == '\\':
            node = self.parse_fn()
        elif tok[1] == '[':
            node = self.parse_list()
        elif tok[1] == '?':
            node = self.parse_if()
        elif tok[1] == '{':
            node = self.parse_block()
        elif tok[0] == 'INT':
            t = self.advance()
            node = Lit(t[1], t[2], t[3])
        elif tok[0] == 'STR':
            t = self.advance()
            node = Lit(t[1], t[2], t[3])
        elif tok[0] == 'NAME':
            t = self.advance()
            node = Ref(t[1], t[2], t[3])
        else:
            self.error(f'expected expression, got {tok[1]!r}')

        while self.peek()[1] == '(':
            self.advance()
            args = self.parse_args()
            self.expect('PUNCT', ')')
            node = Call(node, args, node.line, node.col)

        return node

    def parse_fn(self):
        tok = self.expect('PUNCT', '\\')
        self.expect('PUNCT', '(')
        params = self.parse_params()
        self.expect('PUNCT', ':')
        body = self.parse_expr()
        self.expect('PUNCT', ')')
        return Fn(params, body, tok[2], tok[3])

    def parse_params(self):
        params = []
        while self.peek()[0] == 'NAME':
            params.append(self.advance()[1])
        return params

    def parse_list(self):
        tok = self.expect('PUNCT', '[')
        items = []
        if self.peek()[1] != ']':
            items.append(self.parse_expr())
            while self.peek()[1] == ',':
                self.advance()
                items.append(self.parse_expr())
        self.expect('PUNCT', ']')
        return List(items, tok[2], tok[3])

    def parse_if(self):
        tok = self.expect('PUNCT', '?')
        self.expect('PUNCT', '(')
        cond = self.parse_expr()
        self.expect('PUNCT', ',')
        then = self.parse_expr()
        self.expect('PUNCT', ',')
        else_ = self.parse_expr()
        self.expect('PUNCT', ')')
        return If(cond, then, else_, tok[2], tok[3])

    def parse_block(self):
        tok = self.expect('PUNCT', '{')
        bindings = []
        while self.peek()[1] == '=':
            bindings.append(self.parse_bind())
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


def parse(source, filepath='<input>'):
    tokens = tokenize(source, filepath)
    parser = Parser(tokens, filepath)
    return parser.parse_program()


# === Test ===

if __name__ == '__main__':
    src = r"""
from core.axioms import Extensionality

=(x 5)
=(y add(x, 1))
=(f \(a b : add(a, b)))

=(result {
    =(p mem(z, a))
    =(q implies(p, p))
    forall_right(s1, q, z)
})

=(factorial \(n : ?(eq(n, 0), 1, mul(n, factorial(sub(n, 1))))))
=(test ?(eq(x, 0), x, mul(x, 2)))
=(apply \(f : f(1)(2)))

# lists
=(xs [1, 2, 3])
=(empty [])
=(nested [1, [2, 3], 4])

# deep nested function with call
=(compose \(f g : \(x : f(g(x)))))
=(callnow \(f g : \(x : f(g(x))))(add)(mul)(3))
=(thunk \(: 42))
=(deep \(f : \(g : f(g)(1, 2)))(\(x : \(y : add(x, y))))(\(n : mul(n, 3))))
"""

    ast = parse(src, '<test>')
    for node in ast:
        print(repr(node))
