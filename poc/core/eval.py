"""Evaluator for the min language.

Strict evaluation, lazy only for if-branches.
"""

from parser import parse, Import, Let, Fn as FnAST, Call, Ref, Lit, Block, If
import os


# === Traced: every value carries its AST ===

class Traced:
    def __init__(self, value, ast):
        self.value = value
        self.ast = ast


class Rest:
    def __init__(self, args):
        self.args = args

    def __repr__(self):
        return ', '.join(repr(a) for a in self.args)


# === Env ===

class Env:
    def __init__(self, parent=None):
        self.bindings = {}
        self.parent = parent

    def get(self, name):
        if name in self.bindings:
            return self.bindings[name]
        if self.parent:
            return self.parent.get(name)
        return None

    def set(self, name, value):
        self.bindings[name] = value


# === Fn: runtime function (closure) ===

class Fn:
    def __init__(self, params, rest, body_ast, env):
        self.params = params
        self.rest = rest
        self.body_ast = body_ast
        self.env = env

    def call(self, args):
        child = Env(self.env)
        for p, a in zip(self.params, args):
            child.set(p, a)
        if self.rest:
            rest = args[len(self.params):]
            child.set(self.rest, Traced(rest, Rest(rest)))
        return evaluate(self.body_ast, child)


# === Kernel type wrappers ===

from proof import Var as KVar, In as KIn, Not as KNot, Implies as KImplies, Forall as KForall, Sequent as KSequent, Proof as KProof

class Form:
    pass

class EVar(Form):
    def __init__(self):
        self.kernel = KVar()

class EIn(Form):
    def __init__(self, left, right):
        self.left = left    # Traced
        self.right = right  # Traced
        self.kernel = KIn(left.value, right.value)

class ENot(Form):
    def __init__(self, operand):
        self.operand = operand  # Traced
        self.kernel = KNot(operand.value)

class EImplies(Form):
    def __init__(self, left, right):
        self.left = left    # Traced
        self.right = right  # Traced
        self.kernel = KImplies(left.value, right.value)

class EForall(Form):
    def __init__(self, fn):
        self.fn = fn  # Traced Fn
        v = KVar()
        body = fn.value.call([Traced(v, None)])
        self.kernel = KForall(v, body.value)

class ESequent(Form):
    def __init__(self, left, right):
        self.left = left    # Traced (list of Traced)
        self.right = right  # Traced (list of Traced)
        self.kernel = KSequent([a.value.kernel for a in left.value],
                               [a.value.kernel for a in right.value])

class EProof(Form):
    def __init__(self, sequent, rule, premises=None, term=None, principal=None):
        self.sequent = sequent  # Traced
        self.rule = rule        # Traced
        s = sequent.value.kernel
        r = rule.value
        p = [a.value.kernel for a in premises.value] if premises else []
        t = term.value.kernel if term else None
        pr = principal.value.kernel if principal else None
        self.kernel = KProof(s, r, p, t, pr)


# === Accessors (Traced in, Traced out) ===

class Accessor:
    pass

class ABody(Accessor):
    def __call__(self, f):
        return f.value.fn  # original Traced Fn


# === Builtins ===

BUILTINS = {
    # Arithmetic
    'add': lambda a, b: a + b,
    'sub': lambda a, b: a - b,
    'mul': lambda a, b: a * b,
    # Comparison
    'eq': lambda a, b: a == b,
    'lt': lambda a, b: a < b,
    'gt': lambda a, b: a > b,
    # Bool
    'True': True,
    'False': False,
    'not': lambda a: not a,
    # List
    'head': lambda l: l[0],
    'tail': lambda l: l[1:],
    'nil': lambda l: len(l) == 0,
    'len': lambda l: len(l),
    'nth': lambda l, n: l[n],
    'append': lambda l, x: l + [x],
    'concat': lambda a, b: a + b,
    # Kernel types
    'Var': EVar,
    'In': EIn,
    'Not': ENot,
    'Implies': EImplies,
    'Forall': EForall,
    'Sequent': ESequent,
    'Proof': EProof,
    'body': ABody(),
}


# === Evaluate ===

def evaluate(node, env):
    if isinstance(node, Lit):
        return Traced(node.value, node)

    if isinstance(node, Ref):
        val = env.get(node.name)
        if val is not None:
            return val
        raise NameError(f'{node.line}:{node.col}: undefined: {node.name}')

    if isinstance(node, FnAST):
        return Traced(Fn(node.params, node.rest, node.body, env), node)

    if isinstance(node, If):
        cond = evaluate(node.cond, env)
        return evaluate(node.then, env) if cond.value else evaluate(node.else_, env)

    if isinstance(node, Call):
        fn = evaluate(node.callee, env).value
        args = [evaluate(a, env) for a in node.args]

        if isinstance(fn, type) and issubclass(fn, Form):
            result = fn(*args)
            return Traced(result, node)

        if isinstance(fn, Accessor):
            return fn(*args)

        if callable(fn):
            result = fn(*[a.value for a in args])
            return Traced(result, node)

        if isinstance(fn, Fn):
            result = fn.call(args)
            return Traced(result.value, node)

        raise TypeError(f'{node.line}:{node.col}: not callable')

    if isinstance(node, Block):
        child = Env(env)
        for let in node.bindings:
            child.set(let.name, evaluate(let.expr, child))
        return evaluate(node.expr, child)

    raise ValueError(f'cannot evaluate: {type(node).__name__}')


# === File loading ===

ROOT = os.path.dirname(os.path.abspath(__file__))
_loaded = {}


def _make_global_env():
    env = Env()
    for name, val in BUILTINS.items():
        env.set(name, Traced(val, None))
    return env

_global_env = _make_global_env()


def load_file(filepath):
    abspath = os.path.abspath(filepath)
    if abspath in _loaded:
        return _loaded[abspath]

    exports = {}
    _loaded[abspath] = exports

    with open(filepath) as f:
        source = f.read()

    nodes = parse(source, filepath)

    for node in nodes:
        if isinstance(node, Import):
            _load_import(node)
        elif isinstance(node, Let):
            _global_env.set(node.name, evaluate(node.expr, _global_env))
            exports[node.name] = _global_env.get(node.name)

    return exports


def _load_import(node):
    parts = node.module.split('.')
    filepath = os.path.join(ROOT, *parts) + '.min'
    if not os.path.isfile(filepath):
        return
    imported = load_file(filepath)
    for name in node.names:
        if name in imported:
            _global_env.set(name, imported[name])


# === Entry point ===

if __name__ == '__main__':
    import sys

    if len(sys.argv) > 1:
        filepath = sys.argv[1]
    else:
        src = """
let x = 5
let y = add(x, 1)
let double = [n : mul(n, 2)]
let result = double(y)

let factorial = [n : ?(eq(n, 0), 1, mul(n, factorial(sub(n, 1))))]
let fact5 = factorial(5)

let list = [items... : items]
let mylist = list(1, 2, 3)
let first = head(mylist)
let rest = tail(mylist)
let empty = nil(rest)
let length = len(mylist)

let blk = {
    let a = 10
    let b = 20
    add(a, b)
}

let compose = [f, g : [x : f(g(x))]]
let double_then_add1 = compose([n : add(n, 1)], [n : mul(n, 2)])
let r1 = double_then_add1(3)
let callnow = [a, b : add(a, b)](10, 20)
let thunk = [: 42]
let t1 = thunk()
let nested = [a : [b : add(a, b)]]
let n1 = nested(10)(20)

let a = Var()
let f = Forall([x : In(x, a)])
let fb = body(f)
"""
        nodes = parse(src, '<test>')
        env = _make_global_env()
        for node in nodes:
            if isinstance(node, Let):
                env.set(node.name, evaluate(node.expr, env))

        for name in ['x', 'y', 'result', 'fact5', 'list', 'mylist', 'first', 'rest', 'empty', 'length', 'blk',
                      'r1', 'callnow', 't1', 'n1', 'a', 'f', 'fb']:
            t = env.get(name)
            print(f'{name} = {t.value} <- {t.ast}')
