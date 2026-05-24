"""Evaluator for the min language.

Strict evaluation, lazy only for if-branches.
"""

from parser import parse, Import, Bind, Fn as FnAST, Call, Ref, Lit, List as ListAST, Block, If, Show
from proof import var, mem, neg, implies, forall, sequent, proof, same, axiom, qed
import os


# === Traced: every value carries its AST ===

class Traced:
    def __init__(self, value, ast):
        self.value = value
        self.ast = ast


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
        if name in self.bindings:
            raise NameError(f'cannot reassign: {name}')
        self.bindings[name] = value


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
    'add': lambda a, b: a.value + b.value,
    'sub': lambda a, b: a.value - b.value,
    'mul': lambda a, b: a.value * b.value,
    # Comparison
    'eq': lambda a, b: a.value == b.value,
    'lt': lambda a, b: a.value < b.value,
    'gt': lambda a, b: a.value > b.value,
    # Bool
    'True': True,
    'False': False,
    'not': lambda a: not a.value,
    # List
    'head': lambda l: l.value[0].value,
    'tail': lambda l: l.value[1:],
    'nil': lambda l: len(l.value) == 0,
    'len': lambda l: len(l.value),
    'nth': lambda l, n: l.value[n.value].value,
    'append': lambda l, x: l.value + [x],
    'concat': lambda a, b: a.value + b.value,
    # Kernel
    'mem': lambda l, r: mem(l.value, r.value),
    'neg': lambda o: neg(o.value),
    'implies': lambda l, r: implies(l.value, r.value),
    'forall': lambda v, b: forall(v.value, b.value),
    'sequent': lambda l, r: sequent([a.value for a in l.value], [a.value for a in r.value]),
    'proof': lambda s, r, p=None, pr=None, t=None: proof(
        s.value, r.value,
        [a.value for a in p.value] if p else None,
        pr.value if pr else None,
        t.value if t else None),
    'same': lambda a, b: same(a.value, b.value),
    'axiom': lambda f: axiom(f.value),
    'qed': lambda p: qed(p.value),
}


# === AST expansion for display ===

def _expand_ast(ast, env):
    """Recursively expand Ref nodes to their values' ASTs.
    Returns a new AST with refs resolved. Stops at functions/builtins."""
    if isinstance(ast, Ref):
        val = env.get(ast.name)
        if val is None:
            return ast
        if isinstance(val.value, Fn) or callable(val.value):
            return ast
        if val.ast is not None and val.ast is not ast:
            return _expand_ast(val.ast, env)
        return ast
    if isinstance(ast, Call):
        return Call(_expand_ast(ast.callee, env),
                    [_expand_ast(a, env) for a in ast.args],
                    ast.line, ast.col)
    if isinstance(ast, FnAST):
        return FnAST(ast.params, _expand_ast(ast.body, env), ast.line, ast.col)
    if isinstance(ast, ListAST):
        return ListAST([_expand_ast(i, env) for i in ast.items], ast.line, ast.col)
    if isinstance(ast, If):
        return If(_expand_ast(ast.cond, env),
                  _expand_ast(ast.then, env),
                  _expand_ast(ast.else_, env),
                  ast.line, ast.col)
    if isinstance(ast, Block):
        return Block([Bind(b.name, _expand_ast(b.expr, env), b.line, b.col)
                      for b in ast.bindings],
                     _expand_ast(ast.expr, env),
                     ast.line, ast.col)
    if isinstance(ast, Show):
        return Show(_expand_ast(ast.expr, env), ast.line, ast.col)
    return ast


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
        return Traced(node.value, node)

    if isinstance(node, Ref):
        val = env.get(node.name)
        if val is not None:
            return val
        # Unknown name becomes a fresh Var, stored in env
        v = Traced(var(), node)
        env.set(node.name, v)
        return v

    if isinstance(node, FnAST):
        return Traced(Fn(node.params, node.body, env), node)

    if isinstance(node, ListAST):
        items = [_evaluate(item, env) for item in node.items]
        return Traced(items, node)

    if isinstance(node, Show):
        result = _evaluate(node.expr, env)
        print(repr(_expand_ast(result.ast, env)))
        return result

    if isinstance(node, If):
        cond = _evaluate(node.cond, env)
        return _evaluate(node.then, env) if cond.value else _evaluate(node.else_, env)

    if isinstance(node, Call):
        fn = _evaluate(node.callee, env).value
        args = [_evaluate(a, env) for a in node.args]

        if callable(fn):
            result = fn(*args)
            return Traced(result, node)

        if isinstance(fn, Fn):
            result = fn.call(args)
            return Traced(result.value, node)

        raise EvalError('not callable', node)

    if isinstance(node, Block):
        child = Env(env)
        for b in node.bindings:
            child.set(b.name, _evaluate(b.expr, child))
        return _evaluate(node.expr, child)

    raise EvalError(f'unknown node: {type(node).__name__}', node)


# === File loading ===

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
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
        elif isinstance(node, Bind):
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
                env.set(node.name, evaluate(node.expr, env))

        for name in ['x', 'y', 'result', 'fact5', 'mylist', 'first', 'rest', 'empty', 'length', 'blk',
                      'r1', 'callnow', 't1', 'n1', 'f']:
            t = env.get(name)
            print(f'{name} = {t.value} <- {t.ast}')
