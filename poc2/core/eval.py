"""Node-based eval. Everything is a Node(tag, children) or a leaf (int, bool)."""

import os, sys, parser, proof

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# === Node ===

class Traced:
    def __init__(self, v, name, calls=None):
        self.v = v
        self.name = name
        self.calls = calls or []

    def rewrite(self, pmap):
        return Traced(self.v.rewrite(pmap), self.name, self.calls)

    def eval(self):
        return Traced(self.v.eval(), self.name, self.calls)

    def call(self, args):
        return Traced(self.v.call(args), self.name, self.calls + [args])


def _v(t):
    while isinstance(t, Traced):
        t = t.v
    return t


class Val:
    def __init__(self, val):
        self.val = val

    def rewrite(self, pmap):
        return self

    def eval(self):
        return self


class Param:
    def __init__(self, name):
        self.name = name

    def rewrite(self, pmap):
        return pmap[self] if self in pmap else self

    def eval(self):
        raise RuntimeError(f'unresolved param: {self.name}')


class Ref:
    def __init__(self, name):
        self.name = name
        self.target = None
    def rewrite(self, pmap):
        return self
    def eval(self):
        return self.target.eval()
    def call(self, args):
        return self.target.call(args)

class Fn:
    def __init__(self, body, params):
        self.body = body
        self.params = params

    def rewrite(self, pmap):
        return Fn(self.body.rewrite(pmap), self.params)

    def eval(self):
        return self

    def call(self, args):
        padded = args + [Val(None)] * (len(self.params) - len(args))
        return self.body.rewrite(dict(zip(self.params, padded)))


class If:
    def __init__(self, cond, then, else_):
        self.cond = cond
        self.then = then
        self.else_ = else_

    def rewrite(self, pmap):
        return If(self.cond.rewrite(pmap), self.then.rewrite(pmap), self.else_.rewrite(pmap))

    def eval(self):
        cond = _v(self.cond.eval())
        return self.then.eval() if cond.val else self.else_.eval()


class Call:
    def __init__(self, callee, args):
        self.callee = callee
        self.args = args

    def rewrite(self, pmap):
        return Call(self.callee.rewrite(pmap), [a.rewrite(pmap) for a in self.args])

    def eval(self):
        return self.callee.eval().call([a.eval() for a in self.args]).eval()


class List:
    def __init__(self, elems):
        self.elems = elems

    def rewrite(self, pmap):
        return List([e.rewrite(pmap) for e in self.elems])

    def eval(self):
        return Val([e.eval() for e in self.elems])


def _show(v, depth):
    if isinstance(v, Traced):
        if depth == 0:
            s = v.name
            for call_args in v.calls:
                s = f'{s}({", ".join(_show(a, 0) for a in call_args)})'
            return s
        return _show(v.v, depth - 1)
    if isinstance(v, Val):
        if isinstance(v.val, list):
            return f'[{", ".join(_show(e, depth) for e in v.val)}]'
        if isinstance(v.val, KVar):
            return _show(v.val.name, depth)
        if isinstance(v.val, KMem):
            return f'{_show(v.val.left, depth)} in {_show(v.val.right, depth)}'
        if isinstance(v.val, KNeg):
            return f'~{_show(v.val.operand, depth)}'
        if isinstance(v.val, KImplies):
            return f'{_show(v.val.left, depth)} -> {_show(v.val.right, depth)}'
        if isinstance(v.val, KForall):
            return f'A.{_show(v.val.body, depth)}'
        if isinstance(v.val, KSequent):
            return f'{_show(v.val.left, depth)} {_show(v.val.right, depth)}'
        if isinstance(v.val, KProof):
            return f'|- {_show(v.val.seq, depth)}'
        return str(v.val)
    if isinstance(v, Param):
        return v.name
    if isinstance(v, Ref):
        return f'<{v.name}>'
    if isinstance(v, Fn):
        params = ' '.join(p.name for p in v.params)
        return f'\\{params}: {_show(v.body, depth)}'
    if isinstance(v, Call):
        return f'{_show(v.callee, depth)}({", ".join(_show(a, depth) for a in v.args)})'
    if isinstance(v, List):
        return f'[{", ".join(_show(e, depth) for e in v.elems)}]'
    if isinstance(v, If):
        return f'?({_show(v.cond, depth)}, {_show(v.then, depth)}, {_show(v.else_, depth)})'
    if isinstance(v, Var):
        return f'var("{v.name}")'
    if isinstance(v, Mem):
        return f'mem({_show(v.left, depth)}, {_show(v.right, depth)})'
    if isinstance(v, Neg):
        return f'neg({_show(v.operand, depth)})'
    if isinstance(v, Implies):
        return f'implies({_show(v.left, depth)}, {_show(v.right, depth)})'
    if isinstance(v, Forall):
        return f'forall({_show(v.body, depth)})'
    if isinstance(v, Sequent):
        return f'sequent({_show(v.left, depth)}, {_show(v.right, depth)})'
    if isinstance(v, Proof):
        return f'proof({_show(v.seq, depth)}, {_show(v.rule, depth)})'
    if isinstance(v, Axiom):
        return f'axiom({_show(v.f, depth)})'
    return v.show(depth)


def show(v, name, depth, traced):
    if depth:
        prefix = '$$' if traced else '$'
        print(f'{prefix}{name} {_show(v, depth - 1)}')


def _builtin(name, param_names, fn):
    """Build a node class + Fn factory for a builtin operation.
    fn takes eval'd raw values, returns a value (raw or Val)."""
    class Node:
        def __init__(self, *args):
            self.args = args
            self._name = name
        def rewrite(self, pmap):
            return Node(*[a.rewrite(pmap) for a in self.args])
        def eval(self):
            vals = [_v(a.eval()).val for a in self.args]
            result = fn(*vals)
            return result if isinstance(result, (Val, Traced)) else Val(result)
        def show(self, depth):
            return f'{name}({", ".join(_show(a, depth) for a in self.args)})'
    Node.__name__ = name
    params = [Param(n) for n in param_names]
    return Node, Fn(Node(*params), params)

Add, add = _builtin('add', ['a', 'b'], lambda a, b: a + b)
Sub, sub = _builtin('sub', ['a', 'b'], lambda a, b: a - b)
Eq, eq = _builtin('eq', ['a', 'b'], lambda a, b: a == b)
Not, not_ = _builtin('not', ['a'], lambda a: not a)
None_, none = _builtin('none', ['a'], lambda a: a is None)
Head, head = _builtin('head', ['a'], lambda a: a[0])
Tail, tail = _builtin('tail', ['a'], lambda a: a[1:])
Nil, nil = _builtin('nil', ['a'], lambda a: len(a) == 0)
Len, len_ = _builtin('len', ['a'], lambda a: len(a))
Concat, concat = _builtin('concat', ['a', 'b'], lambda a, b: a + b)
Same, same = _builtin('same', ['a', 'b'], lambda a, b: proof.same(a.kernel, b.kernel))


# === Formula nodes ===

class KVar:
    def __init__(self, name, kernel):
        self.name = name
        self.kernel = kernel

class KMem:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.kernel = proof.mem(_v(left).val.kernel, _v(right).val.kernel)

class KNeg:
    def __init__(self, operand):
        self.operand = operand
        self.kernel = proof.neg(_v(operand).val.kernel)

class KImplies:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.kernel = proof.implies(_v(left).val.kernel, _v(right).val.kernel)

class KForall:
    def __init__(self, body):
        self.body = body
        var = Val(KVar('', proof.var()))
        self.kernel = proof.forall(var.val.kernel, _v(body.call([var]).eval()).val.kernel)

class Var:
    def __init__(self, name):
        self.name = name
        self.var = proof.var()

    def rewrite(self, pmap):
        return Var(self.name.rewrite(pmap))

    def eval(self):
        return Val(KVar(self.name.eval(), self.var))

class Mem:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def rewrite(self, pmap):
        return Mem(self.left.rewrite(pmap), self.right.rewrite(pmap))

    def eval(self):
        return Val(KMem(self.left.eval(), self.right.eval()))

class Neg:
    def __init__(self, operand):
        self.operand = operand

    def rewrite(self, pmap):
        return Neg(self.operand.rewrite(pmap))

    def eval(self):
        return Val(KNeg(self.operand.eval()))

class Implies:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def rewrite(self, pmap):
        return Implies(self.left.rewrite(pmap), self.right.rewrite(pmap))

    def eval(self):
        return Val(KImplies(self.left.eval(), self.right.eval()))

class Forall:
    def __init__(self, body):
        self.body = body

    def rewrite(self, pmap):
        return Forall(self.body.rewrite(pmap))

    def eval(self):
        return Val(KForall(self.body.eval()))

class KSequent:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.kernel = proof.sequent([_v(e).val.kernel for e in _v(left).val], [_v(e).val.kernel for e in _v(right).val])

class KProof:
    def __init__(self, seq, rule, premises, principal, term):
        self.seq = seq
        self.rule = rule
        self.premises = premises
        self.principal = principal
        self.term = term
        self.kernel = proof.proof(
            _v(seq).val.kernel,
            _v(rule).val,
            [_v(p).val.kernel for p in premises.val],
            _v(principal).val.kernel if _v(principal).val is not None else None,
            _v(term).val.kernel if _v(term).val is not None else None)

class Sequent:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def rewrite(self, pmap):
        return Sequent(self.left.rewrite(pmap), self.right.rewrite(pmap))

    def eval(self):
        return Val(KSequent(self.left.eval(), self.right.eval()))

class Proof:
    def __init__(self, seq, rule, premises, principal, term):
        self.seq = seq
        self.rule = rule
        self.premises = premises
        self.principal = principal
        self.term = term

    def rewrite(self, pmap):
        return Proof(
            self.seq.rewrite(pmap),
            self.rule.rewrite(pmap),
            self.premises.rewrite(pmap),
            self.principal.rewrite(pmap),
            self.term.rewrite(pmap))

    def eval(self):
        return Val(KProof(
            self.seq.eval(),
            self.rule.eval(),
            self.premises.eval(),
            self.principal.eval(),
            self.term.eval()))


def var():
    n = Param('name')
    return Fn(Var(n), [n])

def mem():
    a = Param('a')
    b = Param('b')
    return Fn(Mem(a, b), [a, b])

def neg():
    a = Param('a')
    return Fn(Neg(a), [a])

def implies():
    a = Param('a')
    b = Param('b')
    return Fn(Implies(a, b), [a, b])

def forall():
    f = Param('f')
    return Fn(Forall(f), [f])

def sequent():
    l = Param('l')
    r = Param('r')
    return Fn(Sequent(l, r), [l, r])

def proof_():
    s, r, p, pr, t = Param('s'), Param('r'), Param('p'), Param('pr'), Param('t')
    return Fn(Proof(s, r, p, pr, t), [s, r, p, pr, t])

class Axiom:
    def __init__(self, f):
        self.f = f

    def rewrite(self, pmap):
        return Axiom(self.f.rewrite(pmap))

    def eval(self):
        f = self.f.eval()
        proof.axiom(_v(f).val.kernel)
        return f

def axiom_():
    f = Param('f')
    return Fn(Axiom(f), [f])


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
        raise KeyError(name)

    def set(self, name, value):
        if name in self.bindings:
            raise NameError(f'cannot reassign: {name}')
        self.bindings[name] = value


def global_():
    e = Env()
    e.set('True', (Val(True), True))
    e.set('False', (Val(False), True))
    e.set('None', (Val(None), True))
    e.set('none', (none, True))
    e.set('add', (add, True))
    e.set('sub', (sub, True))
    e.set('eq', (eq, True))
    e.set('not', (not_, True))
    e.set('same', (same, True))
    e.set('head', (head, True))
    e.set('tail', (tail, True))
    e.set('nil', (nil, True))
    e.set('len', (len_, True))
    e.set('concat', (concat, True))
    e.set('var', (var(), False))
    e.set('mem', (mem(), True))
    e.set('neg', (neg(), True))
    e.set('implies', (implies(), True))
    e.set('forall', (forall(), True))
    e.set('sequent', (sequent(), True))
    e.set('proof', (proof_(), True))
    e.set('axiom', (axiom_(), False))
    return e


# === Evaluate ===

class EvalError(Exception):
    def __init__(self, msg, node=None):
        self.msg = msg
        self.node = node
    def __str__(self):
        if self.node:
            return f'{self.node.file}:{self.node.line}:{self.node.col}: {self.msg}'
        return self.msg


def evaluate(node, env):
    try:
        return _evaluate(node, env).eval()
    except EvalError:
        raise
    except Exception as e:
        raise EvalError(str(e), node) from e


def _evaluate(node, env):
    if isinstance(node, parser.Lit):
        return Val(node.value)

    if isinstance(node, parser.Ref):
        try:
            ref, traced = env.get(node.name)
            return Traced(ref, node.name) if traced else ref
        except KeyError:
            raise EvalError(f'undefined: {node.name}', node)

    if isinstance(node, parser.Fn):
        params = [Param(name) for name in node.params]
        child = Env(env)
        for p in params:
            child.set(p.name, (p, False))
        body = _evaluate(node.body, child)
        return Fn(body, params)

    if isinstance(node, parser.Block):
        child = Env(env)
        for binding in node.bindings:
            _bind(child, binding, False)
        return _evaluate(node.expr, child)

    if isinstance(node, parser.If):
        return If(_evaluate(node.cond, env), _evaluate(node.then, env), _evaluate(node.else_, env))

    if isinstance(node, parser.Call):
        return Call(_evaluate(node.callee, env), [_evaluate(a, env) for a in node.args])

    if isinstance(node, parser.List):
        return List([_evaluate(e, env) for e in node.elems])

    raise EvalError(f'unknown: {type(node).__name__}', node)


# === File loading ===

_loaded = {}

def load_file(filepath):
    filepath = os.path.normpath(filepath)
    if filepath in _loaded:
        return _loaded[filepath]
    exports = {}
    _loaded[filepath] = exports

    with open(filepath) as f:
        source = f.read()
    env = global_()
    for name, val in exports.items():
        env.set(name, val)
    nodes = parser.parse(source, filepath)

    for node in nodes:
        if isinstance(node, parser.Import):
            _load_import(node, env)
        elif isinstance(node, parser.Bind):
            val = _bind(env, node)
            exports[node.name] = (val, node.traced)

    return exports


def _load_import(node, env):
    parts = node.module.split('.')
    filepath = os.path.join(ROOT, *parts) + '.min'
    if not os.path.isfile(filepath):
        return
    imported = load_file(filepath)
    for name in node.names:
        if name in imported:
            try:
                env.set(name, imported[name])
            except NameError:
                pass


def run(filepath):
    try:
        load_file(filepath)
    except EvalError as e:
        print(e, file=sys.stderr)
        return False
    return True

def _bind(env, node, top=True):
    ref = Ref(node.name)
    env.set(node.name, (ref, node.traced))
    val = evaluate(node.expr, env) if top else _evaluate(node.expr, env)
    ref.target = val
    env.bindings[node.name] = (val, node.traced)
    if top:
        show(val, node.name, node.show, node.traced)
    return val

def _run_src(src):
    env = global_()
    nodes = parser.parse(src, '<test>')
    for node in nodes:
        if isinstance(node, parser.Import):
            _load_import(node, env)
        elif isinstance(node, parser.Bind):
            _bind(env, node)


# === Self-test ===

if __name__ == '__main__':
    src = r'''
$$double \n : add(n, n) !
$r1 double(3) !
$r2 double(add(1, 2)) !
$r3 double(3) !!

$id \x : x !
$r4 id(42) !

$$pair \a b : [a, b] !
$r5 pair(1, 2) !

$$compose \f g : \x : f(g(x)) !
$r6 compose(double, double) !
$r7 compose(double, double)(3) !!

$$apply \f x : f(x) !
$r8 apply(double, 3) !

$abs \n : ?(n, n, 0) !
$r9 abs(True) !
$r10 abs(False) !

$$twice \f : \x : f(f(x)) !
$r11 twice(double) !
$r12 twice(double)(3) !
$r13 (\f: \x: f(x))(double) !
$r14 \x : double(x) !!
$$addx \x : \y : add(x, y) !
$r15 addx(1)(2) !
$r16 addx(1)(2) !!

$r17 head([1, 2, 3]) !
$r18 tail([1, 2, 3]) !
$r19 nil([]) !
$r20 nil([1]) !
$r21 len([1, 2, 3]) !
$r22 concat([1, 2], [3, 4]) !

$r23 not(True) !
$r24 not(False) !
$r25 eq(1, 1) !
$r26 eq(1, 2) !
$r27 sub(10, 3) !
$r28 none(None) !
$r29 none(1) !

$a var("a") !
$b var("b") !
$f1 mem(a, b) !
$f2 neg(f1) !
$f3 implies(f1, f2) !
$f4 forall(\x : mem(x, a)) !
$r30 same(f1, f1) !
$r31 same(f1, f2) !
$r31b same(f1, f2) !!
$r31c same(f1, f2) !!!
$r32 \x: same(x, f2) !
$r32b \x: same(x, f2) !!
$r32c \x: same(x, f2) !!!

from core.derived import and, or, iff, exists, eqv
$d1 and(mem(a, b), mem(b, a)) !
$d2 or(mem(a, b), mem(b, a)) !
$d3 iff(mem(a, b), mem(b, a)) !
$d4 exists(\x : mem(x, a)) !
$d4x exists(\x : iff(mem(x, a), mem(x, a))) !
$d4b exists(\x : mem(x, a)) !!
$d5 exists(\x : mem(x, a)) !!
$d5b exists(\x : mem(x, a)) !!!
$d5c exists(\x : mem(x, a)) !!!!
$d5d exists(\x : mem(x, a)) !!!!!
$d5e exists(\x : mem(x, a)) !!!!!!
$d6 eqv(a, b) !
$d6b eqv(a, b) !!
$d6c eqv(a, b) !!!
$d6d eqv(a, b) !!!!
$d6e eqv(a, b) !!!!!

$s1 sequent([f1], [f1]) !
$s2 sequent([f1, f2], [f3]) !
$p1 proof(s1, "axiom", [], f1, None) !
$p1b proof(s1, "axiom", [], f1, None) !!
$p1c proof(s1, "axiom", [], f1, None) !!!
$p1d proof(s1, "axiom", [], f1, None) !!!!
$p13 proof(s1, "axiom", [], f1, None) !!!!!

from core.axioms import Extensionality, EmptySet, Pairing, Separation, Replacement, _close
$ax1 Extensionality !
$ax2 EmptySet !
$ax3 Pairing !
$ax4 Separation(1, \c: \x: neg(mem(x, c))) !
$ax5 Separation(1, \c: \x: mem(x, c)) !
$ax5b Separation(1, \c: \x: mem(x, c)) !!
$ax5c Separation(1, \c: \x: mem(x, c)) !!!
$ax5d Separation(1, \c: \x: mem(x, c)) !!!!
$ax6 Replacement(0, \x y: mem(y, x)) !
$ax7 Replacement(1, \c: \x y: and(mem(x, c), mem(y, c))) !
$ax8 Separation(2, \c: \d: \x: and(mem(x, c), mem(x, d))) !
$ax9 Separation(3, \c: \d: \e: \x: and(mem(x, c), and(mem(x, d), mem(x, e)))) !
$ax9b Separation(3, \c: \d: \e: \x: and(mem(x, c), and(mem(x, d), mem(x, e)))) !!

$c1 _close !

from tactics import ax, nl, nr, il, ir, fl, fr, ct, wl, wr
$A mem(a, b)
$B mem(b, a)
$imp implies(A, B)

$t1 ax(A) !
$t1b ax(A) !!

$s3 wr(ax(A), sequent([A], [A, B]), B) !
$s4 wl(ax(B), sequent([A, B], [B]), A) !
$s5 il(s3, s4, sequent([A, imp], [B]), imp) !
$imp2 implies(imp, B)
$s6 ir(s5, sequent([A], [imp2]), imp2) !
$top implies(A, imp2)
$s7 ir(s6, sequent([], [top]), top) !
$s7b ir(s6, sequent([], [top]), top) !!

from theorems.logic.modus_ponens import modus_ponens
$mp modus_ponens([a, b], \a: \b: [mem(a, b), mem(b, a)]) !
$mpb modus_ponens([a, b], \a: \b: [mem(a, b), mem(b, a)]) !!
$mpc modus_ponens([a, b], \a: \b: [mem(a, b), mem(b, a)]) !!!
$mpd modus_ponens([a, b], \a: \b: [mem(a, b), mem(b, a)]) !!!!
$mpe modus_ponens([a, b], \a: \b: [mem(a, b), mem(b, a)]) !!!!!
$mpf modus_ponens([a, b], \a: \b: [mem(a, b), mem(b, a)]) !!!!!!
$mpg modus_ponens([a, b], \a: \b: [mem(a, b), mem(b, a)]) !!!!!!!
'''
    _run_src(src)
