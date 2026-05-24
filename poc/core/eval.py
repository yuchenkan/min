"""Evaluator for the min language.

Strict evaluation, lazy only for if-branches.
No Traced — values are raw, env tracks ASTs separately for display.
"""

from parser import parse, Import, Bind, Fn as FnAST, Call, Ref, Lit, List as ListAST, Block, If, Show
from proof import var, mem, neg, implies, forall, sequent, proof, same, axiom, qed
import os


# === Env ===

class Env:
    def __init__(self, parent=None):
        self.bindings = {}
        self.asts = {}
        self.parent = parent

    def get(self, name):
        if name in self.bindings:
            return self.bindings[name]
        if self.parent:
            return self.parent.get(name)
        return None

    def get_ast(self, name):
        if name in self.asts:
            return self.asts[name]
        if self.parent:
            return self.parent.get_ast(name)
        return None

    def set(self, name, value, ast=None):
        if name in self.bindings:
            raise NameError(f'cannot reassign: {name}')
        self.bindings[name] = value
        if ast is not None:
            self.asts[name] = ast


# === Fn: runtime function (closure) ===

class Fn:
    def __init__(self, params, body_ast, env):
        self.params = params
        self.body_ast = body_ast
        self.env = env

    def call(self, args):
        child = Env(self.env)
        for p, a in zip(self.params, args):
            child.set(p, a)
        return _evaluate(self.body_ast, child)


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
    # Kernel
    'mem': lambda l, r: mem(l, r),
    'neg': lambda o: neg(o),
    'implies': lambda l, r: implies(l, r),
    'forall': lambda v, b: forall(v, b),
    'sequent': lambda l, r: sequent(l, r),
    'proof': lambda s, r, p=None, pr=None, t=None: proof(s, r, p, pr, t),
    'same': lambda a, b: same(a, b),
    'axiom': lambda f: axiom(f),
    'qed': lambda p: qed(p),
}



# === Evaluate ===

class EvalError(Exception):
    def __init__(self, msg, node, cause=None):
        self.msg = msg
        self.node = node
        self.cause = cause
    def __str__(self):
        loc = f'{node.line}:{node.col}' if (node := self.node) else '?'
        ast = repr(self.node) if self.node else '?'
        s = f'{loc}: {self.msg}\n  at {ast}'
        if self.cause:
            s += f'\n  caused by: {self.cause}'
        return s


def evaluate(node, env):
    try:
        return _evaluate(node, env)
    except EvalError:
        raise
    except Exception as e:
        raise EvalError(str(e), node, e) from e


def _evaluate(node, env):
    if isinstance(node, Lit):
        return node.value

    if isinstance(node, Ref):
        val = env.get(node.name)
        if val is not None:
            return val
        # Unknown name becomes a fresh Var, stored in env
        v = var()
        env.set(node.name, v, node)
        return v

    if isinstance(node, FnAST):
        return Fn(node.params, node.body, env)

    if isinstance(node, ListAST):
        return [_evaluate(item, env) for item in node.items]

    if isinstance(node, Show):
        return _evaluate(node.expr, env)

    if isinstance(node, If):
        cond = _evaluate(node.cond, env)
        return _evaluate(node.then, env) if cond else _evaluate(node.else_, env)

    if isinstance(node, Call):
        fn = _evaluate(node.callee, env)
        args = [_evaluate(a, env) for a in node.args]

        if callable(fn):
            return fn(*args)

        if isinstance(fn, Fn):
            return fn.call(args)

        raise EvalError('not callable', node)

    if isinstance(node, Block):
        child = Env(env)
        for b in node.bindings:
            child.set(b.name, _evaluate(b.expr, child), b.expr)
        return _evaluate(node.expr, child)

    raise EvalError(f'unknown node: {type(node).__name__}', node)


# === File loading ===

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_loaded = {}


def _make_global_env():
    env = Env()
    for name, val in BUILTINS.items():
        env.set(name, val)
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
        elif isinstance(node, Bind):
            val = evaluate(node.expr, _global_env)
            _global_env.set(node.name, val, node.expr)
            exports[node.name] = val

    return exports


def _load_import(node):
    parts = node.module.split('.')
    filepath = os.path.join(ROOT, *parts) + '.min'
    if not os.path.isfile(filepath):
        return
    imported = load_file(filepath)
    for name in node.names:
        if name in imported and _global_env.get(name) is None:
            _global_env.set(name, imported[name])


# === Entry point ===

if __name__ == '__main__':
    import sys

    if len(sys.argv) > 1:
        filepath = sys.argv[1]
    else:
        src = r"""
$x 5
$y add(x, 1)
$double \(n : mul(n, 2))
$result double(y)

$factorial \(n : ?(eq(n, 0), 1, mul(n, factorial(sub(n, 1)))))
$fact5 factorial(5)

$mylist [1, 2, 3]
$first head(mylist)
$rest tail(mylist)
$empty nil(rest)
$length len(mylist)

$blk {
    $a 10
    $b 20
    add(a, b)
}

$compose \(f g : \(x : f(g(x))))
$double_then_add1 compose(\(n : add(n, 1)), \(n : mul(n, 2)))
$r1 double_then_add1(3)
$callnow \(a b : add(a, b))(10, 20)
$thunk \(: 42)
$t1 thunk()
$nested \(a : \(b : add(a, b)))
$n1 nested(10)(20)

$f forall(vx, mem(vx, va))
"""
        nodes = parse(src, '<test>')
        env = _make_global_env()
        for node in nodes:
            if isinstance(node, Bind):
                val = evaluate(node.expr, env)
                env.set(node.name, val, node.expr)

        for name in ['x', 'y', 'result', 'fact5', 'mylist', 'first', 'rest', 'empty', 'length', 'blk',
                      'r1', 'callnow', 't1', 'n1', 'f']:
            print(f'{name} = {env.get(name)}')
