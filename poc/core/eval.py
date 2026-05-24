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


# === Helpers ===

def _v(t):
    while isinstance(t, Traced):
        t = t.value
    return t

def _kernel(x):
    while isinstance(x, Traced):
        x = x.value
    return x.kernel

def show(t, depth):
    """Show a value. Peels Traced layers based on depth.
    Doesn't peel if value is Var or primitive."""
    if isinstance(t, Traced):
        if depth <= 0:
            return repr(t.ast)
        if not isinstance(t.value, (Traced, Mem, Neg, Implies, Forall, Sequent, Proof, list)):
            return repr(t.ast)
        return show(t.value, depth - 1)
    if isinstance(t, Mem):
        return f'mem({show(t.left, depth)}, {show(t.right, depth)})'
    if isinstance(t, Neg):
        return f'neg({show(t.operand, depth)})'
    if isinstance(t, Implies):
        return f'implies({show(t.left, depth)}, {show(t.right, depth)})'
    if isinstance(t, Forall):
        return f'forall({show(t.var, depth)}, {show(t.body, depth)})'
    if isinstance(t, Sequent):
        l = ', '.join(show(a, depth) for a in _v(t.left))
        r = ', '.join(show(a, depth) for a in _v(t.right))
        return f'[{l}] |- [{r}]'
    if isinstance(t, Proof):
        return f'proof({show(t.seq, depth)})'
    if isinstance(t, list):
        return f'[{", ".join(show(a, depth) for a in t)}]'


# === Eval-level formula types ===

class Var:
    def __init__(self, kernel):
        self.kernel = kernel

class Mem:
    def __init__(self, left, right):
        self.left = left    # Traced
        self.right = right  # Traced
        self.kernel = mem(_kernel(_v(left)), _kernel(_v(right)))

class Neg:
    def __init__(self, operand):
        self.operand = operand  # Traced
        self.kernel = neg(_kernel(_v(operand)))

class Implies:
    def __init__(self, left, right):
        self.left = left    # Traced
        self.right = right  # Traced
        self.kernel = implies(_kernel(_v(left)), _kernel(_v(right)))

class Forall:
    def __init__(self, v, body):
        self.var = v      # Traced
        self.body = body  # Traced
        self.kernel = forall(_kernel(_v(v)), _kernel(_v(body)))

class Sequent:
    def __init__(self, left, right):
        self.left = left    # Traced list of Traced
        self.right = right  # Traced list of Traced
        self.kernel = sequent([_kernel(_v(a)) for a in _v(left)], [_kernel(_v(a)) for a in _v(right)])

class Proof:
    def __init__(self, seq, rule, premises=None, principal=None, term=None):
        self.seq = seq          # Traced
        self.rule = rule        # Traced
        self.premises = premises  # list of Traced
        self.principal = principal  # Traced or None
        self.term = term        # Traced or None
        self.kernel = proof(
            _kernel(_v(seq)), _v(rule),
            [_kernel(_v(a)) for a in _v(premises)] if premises else None,
            _kernel(_v(principal)) if principal else None,
            _kernel(_v(term)) if term else None)


# === Builtins ===

class _notrace:
    """Builtin whose result is not wrapped in Traced by evaluator."""
    def __init__(self, fn): self.fn = fn
    def __call__(self, *args): return self.fn(*args)

BUILTINS = {
    # Arithmetic
    'add': lambda a, b: _v(a) + _v(b),
    'sub': lambda a, b: _v(a) - _v(b),
    'mul': lambda a, b: _v(a) * _v(b),
    # Comparison
    'eq': lambda a, b: _v(a) == _v(b),
    'lt': lambda a, b: _v(a) < _v(b),
    'gt': lambda a, b: _v(a) > _v(b),
    # Bool
    'True': True,
    'False': False,
    'not': lambda a: not _v(a),
    # List
    'head': _notrace(lambda l: _v(l)[0]),
    'tail': lambda l: _v(l)[1:],
    'nil': lambda l: len(_v(l)) == 0,
    'len': lambda l: len(_v(l)),
    'nth': _notrace(lambda l, n: _v(l)[_v(n)]),
    'append': lambda l, x: _v(l) + [x],
    'concat': lambda a, b: _v(a) + _v(b),
    # Kernel
    'mem': lambda l, r: Mem(l, r),
    'neg': lambda o: Neg(o),
    'implies': lambda l, r: Implies(l, r),
    'forall': lambda v, b: Forall(v, b),
    'sequent': lambda l, r: Sequent(l, r),
    'proof': lambda s, r, p=None, pr=None, t=None: Proof(s, r, p, pr, t),
    'same': lambda a, b: same(_kernel(_v(a)), _kernel(_v(b))),
    'axiom': lambda f: axiom(_kernel(_v(f))),
    'qed': lambda p: qed(_kernel(_v(p))) or _v(p),
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
        v = Traced(Var(var()), node)
        env.set(node.name, v)
        return v

    if isinstance(node, FnAST):
        return Traced(Fn(node.params, node.body, env), node)

    if isinstance(node, ListAST):
        items = [_evaluate(item, env) for item in node.items]
        return Traced(items, node)

    if isinstance(node, Show):
        depth = 0
        inner = node
        while isinstance(inner, Show):
            depth += 1
            inner = inner.expr
        result = _evaluate(inner, env)
        print(show(result, depth - 1))
        return result

    if isinstance(node, If):
        cond = _evaluate(node.cond, env)
        return _evaluate(node.then, env) if _v(cond) else _evaluate(node.else_, env)

    if isinstance(node, Call):
        fn = _v(_evaluate(node.callee, env))
        args = [_evaluate(a, env) for a in node.args]

        if callable(fn):
            result = fn(*args)
            if isinstance(fn, _notrace):
                return result
            return Traced(result, node)

        if isinstance(fn, Fn):
            result = fn.call(args)
            return Traced(result, node)

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
