"""Pure eval. Closures, immutable env, thin Python wrapper."""

import os, sys, parser, kernel

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# === Env (immutable extend) ===

class Env:
    def __init__(self, parent=None, name=None, val=None):
        self.parent = parent
        self.name = name
        self.val = val

    def get(self, name):
        if self.name == name:
            return self.val
        if self.parent:
            return self.parent.get(name)
        raise KeyError(name)

    def extend(self, name, val):
        return Env(self, name, val)


# === Values (Python objects) ===

class Fn:
    def __init__(self, params, body, env):
        self.params = params
        self.body = body
        self.env = env

    def __repr__(self):
        return f'\\{" ".join(self.params)}: ...'


# === Eval ===

class EvalError(Exception):
    def __init__(self, msg, node=None):
        self.msg = msg
        self.node = node
    def __str__(self):
        if self.node:
            return f'{self.node.file}:{self.node.line}:{self.node.col}: {self.msg}'
        return self.msg


def evaluate(node, env):
    if isinstance(node, parser.Lit):
        return node.value

    if isinstance(node, parser.Ref):
        try:
            return env.get(node.name)
        except KeyError:
            raise EvalError(f'undefined: {node.name}', node)

    if isinstance(node, parser.Fn):
        return Fn(node.params, node.body, env)

    if isinstance(node, parser.Block):
        for binding in node.bindings:
            val = evaluate(binding.expr, env)
            env = env.extend(binding.name, val)
        return evaluate(node.expr, env)

    if isinstance(node, parser.If):
        cond = evaluate(node.cond, env)
        if cond is True:
            return evaluate(node.then, env)
        if cond is False:
            return evaluate(node.else_, env)
        raise EvalError('condition must be True or False', node)

    if isinstance(node, parser.Call):
        callee = evaluate(node.callee, env)
        args = [evaluate(a, env) for a in node.args]
        return call(callee, args, node)

    if isinstance(node, parser.List):
        return [evaluate(e, env) for e in node.elems]

    raise EvalError(f'unknown: {type(node).__name__}', node)


def call(callee, args, node=None):
    if isinstance(callee, Fn):
        env = callee.env
        for i, p in enumerate(callee.params):
            env = env.extend(p, args[i] if i < len(args) else None)
        return evaluate(callee.body, env)
    if callable(callee):
        return callee(*args)
    raise EvalError(f'not callable: {callee}', node)


# === Formula bridge ===

def build(f):
    if isinstance(f, str):
        return f
    tag = f[0]
    if tag == 'mem': return kernel.Mem(build(f[1]), build(f[2]))
    if tag == 'neg': return kernel.Neg(build(f[1]))
    if tag == 'implies': return kernel.Implies(build(f[1]), build(f[2]))
    if tag == 'forall': return kernel.Forall(f[1], build(f[2]))
    raise ValueError(f'build: unknown tag {tag}')

def _do_proof(left, right, rule, premises, principal, term=None):
    seq = kernel.Sequent(
        [build(f) for f in left],
        [build(f) for f in right])
    return kernel.proof(seq, rule, premises, build(principal), term)

def _do_qed(p, expected):
    kernel.qed(p, build(expected))


# === Builtins ===

def _global():
    env = Env()
    env = env.extend('True', True)
    env = env.extend('False', False)
    env = env.extend('None', None)
    env = env.extend('add', lambda a, b: a + b)
    env = env.extend('sub', lambda a, b: a - b)
    env = env.extend('mul', lambda a, b: a * b)
    env = env.extend('eq', lambda a, b: a == b)
    env = env.extend('not', lambda a: not a)
    env = env.extend('head', lambda a: a[0])
    env = env.extend('tail', lambda a: a[1:])
    env = env.extend('len', lambda a: len(a))
    env = env.extend('print', lambda a: print(a) or a)
    env = env.extend('_do_proof', _do_proof)
    env = env.extend('_do_qed', _do_qed)
    return env


# === File loading ===

_loaded = {}

def load_file(filepath):
    filepath = os.path.normpath(filepath)
    if filepath in _loaded:
        return _loaded[filepath]
    _loaded[filepath] = {}

    with open(filepath) as f:
        source = f.read()
    nodes = parser.parse(source, filepath)
    env = _global()

    for node in nodes:
        if isinstance(node, parser.Import):
            env = _load_import(node, env)
        elif isinstance(node, parser.Bind):
            val = evaluate(node.expr, env)
            env = env.extend(node.name, val)
            _loaded[filepath][node.name] = val

    return _loaded[filepath]


def _load_import(node, env):
    parts = node.module.split('.')
    filepath = os.path.join(ROOT, *parts) + '.min'
    if not os.path.isfile(filepath):
        return env
    imported = load_file(filepath)
    for name in node.names:
        if name in imported:
            env = env.extend(name, imported[name])
    return env


def run(filepath):
    try:
        load_file(filepath)
    except EvalError as e:
        print(e, file=sys.stderr)
        return False
    return True


# === Self-test ===

if __name__ == '__main__':
    if len(sys.argv) > 1:
        ok = run(sys.argv[1])
        sys.exit(0 if ok else 1)

    src = r'''
$double \n: add(n, n)
$r1 print(double(3))
$r2 print(double(add(1, 2)))

$id \x: x
$r3 print(id(42))

$pair \a b: [a, b]
$r4 print(pair(1, 2))

$compose \f g: \x: f(g(x))
$quadruple compose(double, double)
$r5 print(quadruple(3))

$fact \self n: ?(eq(n, 0), 1, mul(n, self(self, sub(n, 1))))
$r6 print(fact(fact, 5))
'''
    env = _global()
    nodes = parser.parse(src, '<test>')
    for node in nodes:
        if isinstance(node, parser.Bind):
            val = evaluate(node.expr, env)
            env = env.extend(node.name, val)
