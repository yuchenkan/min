"""Pure eval. Closures, immutable env, thin Python wrapper."""

import os, sys, parser, kernel

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# === Env (immutable extend) ===

class Env:
    __slots__ = ('d',)
    def __init__(self, d=None):
        self.d = d if d is not None else {}

    def get(self, name):
        return self.d[name]

    def snapshot(self):
        return Env(self.d.copy())


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
        self.trace = []
    def add_frame(self, node):
        self.trace.append(node)
    def __str__(self):
        lines = []
        if self.node:
            lines.append(f'{self.node.file}:{self.node.line}:{self.node.col}: {self.msg}')
        else:
            lines.append(self.msg)
        for n in self.trace:
            lines.append(f'  at {n.file}:{n.line}:{n.col}')
        return '\n'.join(lines)


def _eval_lit(node, env):
    return node.value

def _eval_ref(node, env):
    try:
        return env.get(node.name)
    except KeyError:
        raise EvalError(f'undefined: {node.name}', node)

def _eval_fn(node, env):
    return Fn(node.params, node.body, env.snapshot())

def _eval_block(node, env):
    env = env.snapshot()
    for binding in node.bindings:
        val = evaluate(binding.expr, env)
        env.d[binding.name] = val
    return evaluate(node.expr, env)

def _eval_if(node, env):
    cond = evaluate(node.cond, env)
    if cond is True:
        return evaluate(node.then, env)
    if cond is False:
        return evaluate(node.else_, env)
    raise EvalError('condition must be True or False', node)

def _eval_call(node, env):
    callee = evaluate(node.callee, env)
    args = [evaluate(a, env) for a in node.args]
    try:
        return call(callee, args, node)
    except EvalError as e:
        e.add_frame(node)
        raise

def _eval_list(node, env):
    return [evaluate(e, env) for e in node.elems]

_DISPATCH = {
    parser.Lit: _eval_lit,
    parser.Ref: _eval_ref,
    parser.Fn: _eval_fn,
    parser.Block: _eval_block,
    parser.If: _eval_if,
    parser.Call: _eval_call,
    parser.List: _eval_list,
}

def evaluate(node, env):
    f = _DISPATCH.get(type(node))
    if f:
        return f(node, env)
    raise EvalError(f'unknown: {type(node).__name__}', node)


def call(callee, args, node=None):
    if isinstance(callee, Fn):
        env = callee.env.snapshot()
        for i, p in enumerate(callee.params):
            env.d[p] = args[i] if i < len(args) else None
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
    try:
        seq = kernel.Sequent(
            [build(f) for f in left],
            [build(f) for f in right])
        return [True, kernel.proof(seq, rule, premises, build(principal), term)]
    except (ValueError, TypeError) as e:
        return [False, str(e)]

def _do_qed(p, expected, system):
    try:
        kernel.qed(p, build(expected), system)
        return [True, None]
    except (ValueError, TypeError) as e:
        return [False, str(e)]

def _fail(msg):
    raise EvalError(msg)


# === Builtins ===

def _global():
    return Env({
        'True': True, 'False': False, 'None': None,
        'add': lambda a, b: a + b, 'sub': lambda a, b: a - b,
        'mul': lambda a, b: a * b, 'eq': lambda a, b: a == b,
        'not': lambda a: not a,
        'head': lambda a: a[0], 'tail': lambda a: a[1:],
        'len': lambda a: len(a), 'print': lambda a: print(a) or a,
        '_do_proof': _do_proof, '_do_qed': _do_qed, '_fail': _fail,
    })


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
            _load_import(node, env)
        elif isinstance(node, parser.Bind):
            val = evaluate(node.expr, env)
            env.d[node.name] = val
            _loaded[filepath][node.name] = val

    return _loaded[filepath]


def _load_import(node, env):
    parts = node.module.split('.')
    filepath = os.path.join(ROOT, *parts) + '.min'
    if not os.path.isfile(filepath):
        return
    imported = load_file(filepath)
    for name in node.names:
        if name in imported:
            env.d[name] = imported[name]


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
