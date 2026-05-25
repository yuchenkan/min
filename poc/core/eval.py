"""Evaluator for the min language.

Every value is Traced(value, ast). The ast is the Call/Ref/Lit node
that produced the value — the vocab-level display.
"""

from parser import parse, Import, Bind, Fn as FnAST, Call, Ref, Lit, List as ListAST, Block, If, Show
from proof import var, mem, neg, implies, forall, sequent, proof, same, axiom, qed
import os


# === Traced ===

class Traced:
    def __init__(self, value, callee, args):
        self.value = value
        self.callee = callee
        self.args = args


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
    def __init__(self, params, body_ast, env, traced=False):
        self.params = params
        self.body_ast = body_ast
        self.env = env
        self.traced = traced

    def call(self, args):
        child = Env(self.env)
        for p, a in zip(self.params, args):
            child.set(p, a)
        return evaluate(self.body_ast, child)


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
            return f'{repr(t.callee)}({", ".join([show(a, 0) for a in t.args])})'
        return show(t.value, depth - 1)
    if isinstance(t, Var):
        return t.name
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
    if isinstance(t, bool):
        return str(t)
    if isinstance(t, (int, float)):
        return str(t)
    if isinstance(t, str):
        return '"' + t.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\t', '\\t') + '"'
    if isinstance(t, Fn):
        s = '\\\\' if t.traced else '\\'
        return f'{s}({" ".join(t.params)} : {t.body_ast!r})'
    raise ValueError(f'show: unexpected {type(t).__name__}')


# === Eval-level formula types ===

class Var:
    def __init__(self, kernel, name):
        self.kernel = kernel
        self.name = name

class Mem:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.kernel = mem(_kernel(_v(left)), _kernel(_v(right)))

class Neg:
    def __init__(self, operand):
        self.operand = operand 
        self.kernel = neg(_kernel(_v(operand)))

class Implies:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.kernel = implies(_kernel(_v(left)), _kernel(_v(right)))

class Forall:
    def __init__(self, v, body):
        self.var = v
        self.body = body
        self.kernel = forall(_kernel(_v(v)), _kernel(_v(body)))

class Sequent:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.kernel = sequent([_kernel(_v(a)) for a in _v(left)], [_kernel(_v(a)) for a in _v(right)])

class Proof:
    def __init__(self, seq, rule, premises=None, principal=None, term=None):
        self.seq = seq
        self.rule = rule
        self.premises = premises
        self.principal = principal
        self.term = term
        try:
            self.kernel = proof(
                _kernel(_v(seq)), _v(rule),
                [_kernel(_v(a)) for a in _v(premises)] if premises else None,
                _kernel(_v(principal)) if principal else None,
                _kernel(_v(term)) if term else None)
        except ValueError as e:
            parts = [f'{e}']
            parts.append(f'  sequent:   {show(seq, 0)}')
            parts.append(f'  rule:      {_v(rule)}')
            if premises:
                for i, p in enumerate(_v(premises)):
                    parts.append(f'  premise[{i}]: {show(p, 0)}')
            if principal:
                parts.append(f'  principal: {show(principal, 0)}')
            if term:
                parts.append(f'  term:      {show(term, 0)}')
            raise ValueError('\n'.join(parts)) from None


def _qed(p, e):
    """Check proof against expected formula and show level 0 equality."""
    qed(_kernel(_v(p)), _kernel(_v(e)))
    s_proof = show(_v(_v(p).seq.right)[0], 0)
    s_expected = show(e, 0)
    if s_proof != s_expected:
        raise ValueError(f'qed: show mismatch\n  proof:    {s_proof}\n  expected: {s_expected}')
    return p


# === Builtins ===

class _notrace:
    """Builtin whose result is not wrapped in Traced by evaluator."""
    def __init__(self, fn): self.fn = fn
    def __call__(self, *args): return self.fn(*args)

BUILTINS = {
    # Arithmetic
    'add': _notrace(lambda a, b: _v(a) + _v(b)),
    'sub': _notrace(lambda a, b: _v(a) - _v(b)),
    'mul': _notrace(lambda a, b: _v(a) * _v(b)),
    # Comparison
    'eq': _notrace(lambda a, b: _v(a) == _v(b)),
    'lt': _notrace(lambda a, b: _v(a) < _v(b)),
    'gt': _notrace(lambda a, b: _v(a) > _v(b)),
    # Bool
    'True': True,
    'False': False,
    'not': _notrace(lambda a: not _v(a)),
    # List
    'head': _notrace(lambda l: _v(l)[0]),
    'tail': _notrace(lambda l: _v(l)[1:]),
    'nil': _notrace(lambda l: len(_v(l)) == 0),
    'len': _notrace(lambda l: len(_v(l))),
    'nth': _notrace(lambda l, n: _v(l)[_v(n)]),
    'append': _notrace(lambda l, x: _v(l) + [x]),
    'concat': _notrace(lambda a, b: _v(a) + _v(b)),
    # Kernel
    'mem': _notrace(lambda l, r: Mem(l, r)),
    'neg': _notrace(lambda o: Neg(o)),
    'implies': _notrace(lambda l, r: Implies(l, r)),
    'forall': _notrace(lambda v, b: Forall(v, b)),
    'sequent': _notrace(lambda l, r: Sequent(l, r)),
    'proof': _notrace(lambda s, r, p=None, pr=None, t=None: Proof(s, r, p, pr, t)),
    'same': _notrace(lambda a, b: same(_kernel(_v(a)), _kernel(_v(b)))),
    'axiom': _notrace(lambda f: axiom(_kernel(_v(f))) or f),
    'qed': _notrace(lambda p, e: _qed(p, e)),
}



# === Evaluate ===

class EvalError(Exception):
    def __init__(self, msg, node, cause=None):
        self.msg = msg
        self.node = node
        self.cause = cause
        self.stack = []

    def _loc(self, node):
        f = f'{node.file}:' if hasattr(node, 'file') and node.file else ''
        return f'{f}{node.line}:{node.col}'

    def add_frame(self, node):
        self.stack.append(node)

    def __str__(self):
        loc = self._loc(self.node) if self.node else '?'
        msg = self.msg.replace('\n', '\n  ')
        s = f'error: {loc}: {msg}'
        if self.node:
            s += f'\n  at {self.node!r}'
        for frame in self.stack:
            s += f'\n  in {self._loc(frame)} {frame!r}'
        return s


def evaluate(node, env):
    try:
        return _evaluate(node, env)
    except EvalError:
        raise
    except Exception as e:
        raise EvalError(str(e), node, e) from None


def _evaluate(node, env):
    if isinstance(node, Lit):
        return node.value

    if isinstance(node, Ref):
        val = env.get(node.name)
        if val is not None:
            return val
        v = Var(var(), node.name)
        env.set(node.name, v)
        return v

    if isinstance(node, FnAST):
        return Fn(node.params, node.body, env, node.traced)

    if isinstance(node, ListAST):
        return [_evaluate(item, env) for item in node.items]

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

        try:
            if callable(fn):
                result = fn(*args)
                if isinstance(fn, _notrace):
                    return result
                return Traced(result, node.callee, args)

            if isinstance(fn, Fn):
                result = fn.call(args)
                return Traced(result, node.callee, args) if fn.traced else result
        except EvalError as e:
            e.add_frame(node)
            raise
        except Exception as e:
            raise EvalError(str(e), node, e) from None

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


def run(filepath):
    """Run a .min file. Catches EvalError and prints cleanly."""
    import sys
    try:
        load_file(filepath)
    except EvalError as e:
        print(e, file=sys.stderr)
        return False
    return True


if __name__ == '__main__':
    import sys

    if len(sys.argv) > 1:
        ok = run(sys.argv[1])
        sys.exit(0 if ok else 1)

    # Self-test: show with formulas and traced computation
    load_file(os.path.join(ROOT, 'core', 'derived.min'))

    src = r'''
$A mem(a, b)
$B mem(b, a)
$f1 and(A, B)
$f2 or(A, B)
$f3 iff(A, B)
$f4 exists(x, mem(x, a))
$f5 eqv(a, b)
$f6 implies(f1, f2)
$f7 forall(a, implies(mem(a, b), exists(x, and(mem(x, a), mem(x, b)))))

$double \\(n : mul(n, 2))
$r1 double(3)
$r2 double(add(1, 2))
$compose \\(f g : \\(x : f(g(x))))
$double_add1 compose(double, \\(n : add(n, 1)))
$r3 double_add1(3)
'''
    nodes = parse(src, '<test>')
    for node in nodes:
        if isinstance(node, Bind):
            _global_env.set(node.name, evaluate(node.expr, _global_env))

    tests = ['f1', 'f2', 'f3', 'f4', 'f5', 'f6', 'f7', 'r1', 'r2', 'r3', 'double_add1']
    for name in tests:
        v = _global_env.get(name)
        print(f'--- {name} ---')
        for d in range(4):
            print(f'  {d}: {show(v, d)}')
