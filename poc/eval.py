"""Evaluator for the min language.

Strict evaluation, lazy only for if-branches.
Every value carries its computation trace.
Name fallback creates Var and stores in env.
"""

from parser import parse, Import, Bind, Call, Ref, Lit, Block
import os


# === Trace: every value wraps (fn, args, result) ===

class Traced:
    """Value with computation trace."""
    def __init__(self, value, trace=None):
        self.value = value
        self.trace = trace  # (name, args) or None for literals

    def show(self, level=0):
        if level == 0 and self.trace:
            name, args = self.trace
            if args:
                return f'{name}({", ".join(a.show(0) if isinstance(a, Traced) else str(a) for a in args)})'
            return name
        return str(self.value)


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


# === Fn: user-defined function ===

class Fn:
    def __init__(self, name, params, body_ast, env):
        self.name = name
        self.params = params
        self.body_ast = body_ast
        self.env = env

    def call(self, args):
        child = Env(self.env)
        for p, a in zip(self.params, args):
            child.set(p, a)
        return evaluate(self.body_ast, child)


# === Builtins ===

def _builtin(name, fn):
    return (name, fn)

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
    # Pair
    'Pair': lambda a, b: (a, b),
    'fst': lambda p: p[0],
    'snd': lambda p: p[1],
    # List (from pairs)
    'Nil': None,
    'Cons': lambda h, t: (h, t),
    'head': lambda l: l[0],
    'tail': lambda l: l[1],
    'nil': lambda l: l is None,
    # String
    'concat': lambda a, b: a + b,
    'len': lambda s: len(s),
}


# === Evaluate ===

def evaluate(node, env):
    if isinstance(node, Lit):
        return node.value

    if isinstance(node, Ref):
        val = env.get(node.name)
        if val is not None:
            return val
        # Name fallback: create Var-like object, store in env
        # (For formula layer — bare names become variables)
        raise NameError(f'{node.line}:{node.col}: undefined: {node.name}')

    if isinstance(node, Call):
        # Special form: if (lazy branches)
        if node.name == 'if':
            cond = evaluate(node.args[0], env)
            if cond:
                return evaluate(node.args[1], env)
            else:
                return evaluate(node.args[2], env)

        fn = env.get(node.name)
        if fn is None:
            raise NameError(f'{node.line}:{node.col}: undefined: {node.name}')

        args = [evaluate(a, env) for a in node.args]

        # Builtin function
        if callable(fn):
            result = fn(*args)
            return Traced(result, (node.name, args)).value if not isinstance(result, Traced) else result

        # User-defined Fn
        if isinstance(fn, Fn):
            return fn.call(args)

        raise TypeError(f'{node.line}:{node.col}: {node.name} is not callable')

    if isinstance(node, Block):
        child = Env(env)
        for binding in node.bindings:
            _eval_binding(binding, child)
        return evaluate(node.expr, child)

    if isinstance(node, Bind):
        _eval_binding(node, env)
        return None

    raise ValueError(f'cannot evaluate: {type(node).__name__}')


def _eval_binding(node, env):
    if node.params:
        fn = Fn(node.name, node.params, node.body, env)
        env.set(node.name, fn)
    else:
        val = evaluate(node.body, env)
        env.set(node.name, val)


# === File loading ===

ROOT = os.path.dirname(os.path.abspath(__file__))
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
            _eval_binding(node, _global_env)
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
        # Inline test
        src = """
x = 5
y = add(x, 1)
double(n) = mul(n, 2)
result = double(y)

factorial(n) = if(eq(n, 0), 1, mul(n, factorial(sub(n, 1))))
fact5 = factorial(5)

p = Pair(1, 2)
first = fst(p)

blk = {
    a = 10
    b = 20
    add(a, b)
}
"""
        nodes = parse(src, '<test>')
        env = _make_global_env()
        for node in nodes:
            _eval_binding(node, env)

        for name in ['x', 'y', 'result', 'fact5', 'first', 'blk']:
            print(f'{name} = {env.get(name)}')
