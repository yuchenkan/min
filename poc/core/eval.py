"""Evaluator for the min language.

Every value is Traced(value, ast). The ast is the Call/Ref/Lit node
that produced the value — the vocab-level display.
"""

from parser import parse, Import, Bind, Fn as FnAST, Call, Ref, Lit, List as ListAST, Block, If, Show
from proof import var, mem, neg, implies, forall, sequent, proof, same, axiom, qed
import os


# === Traced ===

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


# === Fn ===

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
# All receive Traced args. Return raw values. Evaluator wraps result.

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



# === Evaluate ===

class EvalError(Exception):
    def __init__(self, msg, node, cause=None):
        self.msg = msg
        self.node = node
        self.cause = cause
    def __str__(self):
        loc = f'{node.line}:{node.col}' if (node := self.node) else '?'
        s = f'{loc}: {self.msg}'
        if self.node:
            s += f'\n  at {self.node!r}'
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
        v = Traced(var(), node)
        env.set(node.name, v)
        return v

    if isinstance(node, FnAST):
        return Traced(Fn(node.params, node.body, env), node)

    if isinstance(node, ListAST):
        items = [_evaluate(item, env) for item in node.items]
        return Traced(items, node)

    if isinstance(node, Show):
        return _evaluate(node.expr, env)

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
