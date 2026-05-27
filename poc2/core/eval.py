"""Node-based eval. Everything is a Node(tag, children) or a leaf (int, bool)."""

import os, sys, parser, proof

ROOT = os.path.dirname(os.path.abspath(__file__))


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
        return str(v.val)
    if isinstance(v, Param):
        return v.name
    if isinstance(v, Fn):
        params = ' '.join(p.name for p in v.params)
        return f'\\({params} : {_show(v.body, depth)})'
    if isinstance(v, Call):
        return f'{_show(v.callee, depth)}({", ".join(_show(a, depth) for a in v.args)})'
    if isinstance(v, List):
        return f'[{", ".join(_show(e, depth) for e in v.elems)}]'
    if isinstance(v, If):
        return f'?({_show(v.cond, depth)}, {_show(v.then, depth)}, {_show(v.else_, depth)})'
    if isinstance(v, Add):
        return f'add({_show(v.a, depth)}, {_show(v.b, depth)})'
    if isinstance(v, Var):
        return v.name
    if isinstance(v, Mem):
        return f'mem({_show(v.left, depth)}, {_show(v.right, depth)})'
    if isinstance(v, Neg):
        return f'neg({_show(v.operand, depth)})'
    if isinstance(v, Implies):
        return f'implies({_show(v.left, depth)}, {_show(v.right, depth)})'
    if isinstance(v, Forall):
        return f'forall(\\({v.var.name} : {_show(v.body, depth)}))'
    if isinstance(v, Sequent):
        l = ', '.join(_show(a, depth) for a in v.left)
        r = ', '.join(_show(a, depth) for a in v.right)
        return f'[{l}] |- [{r}]'


def show(v, name, depth, traced):
    if depth:
        prefix = '$$' if traced else '$'
        print(f'{prefix}{name} {_show(v, depth - 1)}')


class Add:
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def rewrite(self, pmap):
        return Add(self.a.rewrite(pmap), self.b.rewrite(pmap))

    def eval(self):
        return Val(_v(self.a).val + _v(self.b).val)


class Sub:
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def rewrite(self, pmap):
        return Sub(self.a.rewrite(pmap), self.b.rewrite(pmap))

    def eval(self):
        return Val(_v(self.a).val - _v(self.b).val)

class Eq:
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def rewrite(self, pmap):
        return Eq(self.a.rewrite(pmap), self.b.rewrite(pmap))

    def eval(self):
        return Val(_v(self.a).val == _v(self.b).val)

class Not:
    def __init__(self, a):
        self.a = a

    def rewrite(self, pmap):
        return Not(self.a.rewrite(pmap))

    def eval(self):
        return Val(not _v(self.a).val)

def add():
    a, b = Param('a'), Param('b')
    return Fn(Add(a, b), [a, b])

def sub():
    a, b = Param('a'), Param('b')
    return Fn(Sub(a, b), [a, b])

def eq():
    a, b = Param('a'), Param('b')
    return Fn(Eq(a, b), [a, b])

class None_:
    def __init__(self, a):
        self.a = a

    def rewrite(self, pmap):
        return None_(self.a.rewrite(pmap))

    def eval(self):
        return Val(_v(self.a).val is None)

def not_():
    a = Param('a')
    return Fn(Not(a), [a])

def none():
    a = Param('a')
    return Fn(None_(a), [a])

class Same:
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def rewrite(self, pmap):
        return Same(self.a.rewrite(pmap), self.b.rewrite(pmap))

    def eval(self):
        return Val(proof.same(_v(self.a).val, _v(self.b).val))

def same():
    a, b = Param('a'), Param('b')
    return Fn(Same(a, b), [a, b])

class Head:
    def __init__(self, a):
        self.a = a
    def rewrite(self, pmap):
        return Head(self.a.rewrite(pmap))
    def eval(self):
        return _v(self.a).val[0]

class Tail:
    def __init__(self, a):
        self.a = a
    def rewrite(self, pmap):
        return Tail(self.a.rewrite(pmap))
    def eval(self):
        return Val(_v(self.a).val[1:])

class Nil:
    def __init__(self, a):
        self.a = a
    def rewrite(self, pmap):
        return Nil(self.a.rewrite(pmap))
    def eval(self):
        return Val(len(_v(self.a).val) == 0)

class Len:
    def __init__(self, a):
        self.a = a
    def rewrite(self, pmap):
        return Len(self.a.rewrite(pmap))
    def eval(self):
        return Val(len(_v(self.a).val))

class Concat:
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def rewrite(self, pmap):
        return Concat(self.a.rewrite(pmap), self.b.rewrite(pmap))
    def eval(self):
        return Val(_v(self.a).val + _v(self.b).val)

def head():
    a = Param('a')
    return Fn(Head(a), [a])

def tail():
    a = Param('a')
    return Fn(Tail(a), [a])

def nil():
    a = Param('a')
    return Fn(Nil(a), [a])

def len_():
    a = Param('a')
    return Fn(Len(a), [a])

def concat():
    a, b = Param('a'), Param('b')
    return Fn(Concat(a, b), [a, b])


# === Formula nodes ===

class Var:
    def __init__(self, name):
        self.name = name
        self.var = proof.var()

    def rewrite(self, pmap):
        return Var(self.name.rewrite(pmap))

    def eval(self):
        return Val(self.var)

class Mem:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def rewrite(self, pmap):
        return Mem(self.left.rewrite(pmap), self.right.rewrite(pmap))

    def eval(self):
        return Val(proof.mem(_v(self.left.eval()).val, _v(self.right.eval()).val))

class Neg:
    def __init__(self, operand):
        self.operand = operand

    def rewrite(self, pmap):
        return Neg(self.operand.rewrite(pmap))

    def eval(self):
        return Val(proof.neg(_v(self.operand.eval()).val))

class Implies:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def rewrite(self, pmap):
        return Implies(self.left.rewrite(pmap), self.right.rewrite(pmap))

    def eval(self):
        return Val(proof.implies(_v(self.left.eval()).val, _v(self.right.eval()).val))

class Forall:
    def __init__(self, body):
        self.body = body

    def rewrite(self, pmap):
        return Forall(self.body.rewrite(pmap))

    def eval(self):
        v = Val(proof.var())
        return Val(proof.forall(v.val, _v(self.body.call([v]).eval()).val))

class Sequent:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def rewrite(self, pmap):
        return Sequent([e.rewrite(pmap) for e in self.left], [e.rewrite(pmap) for e in self.right])

    def eval(self):
        return proof.sequent([e.eval().val for e in self.left], [e.eval().val for e in self.right])


class Proof:
    def __init__(self, seq, rule, premises, principal, term):
        self.seq = seq
        self.rule = rule
        self.premises = premises
        self.principal = principal
        self.term = term

    def rewrite(self, pmap):
        return self

    def eval(self):
        return proof.proof(
            self.seq.eval().val,
            self.rule.eval().val,
            [p.eval().val for p in self.premises],
            self.principal.eval().val if self.principal else None,
            self.term.eval().val if self.term else None)


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
    e.set('none', (none(), True))
    e.set('add', (add(), True))
    e.set('sub', (sub(), True))
    e.set('eq', (eq(), True))
    e.set('not', (not_(), True))
    e.set('same', (same(), True))
    e.set('head', (head(), True))
    e.set('tail', (tail(), True))
    e.set('nil', (nil(), True))
    e.set('len', (len_(), True))
    e.set('concat', (concat(), True))
    e.set('var', (var(), True))
    e.set('mem', (mem(), True))
    e.set('neg', (neg(), True))
    e.set('implies', (implies(), True))
    e.set('forall', (forall(), True))
    e.set('sequent', (sequent(), True))
    e.set('proof_', (proof_(), True))
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
            val = evaluate(binding.expr, child)
            show(val, binding.name, binding.show, binding.traced)
            child.set(binding.name, (val, binding.traced))
        return _evaluate(node.expr, child)

    if isinstance(node, parser.If):
        return If(_evaluate(node.cond, env), _evaluate(node.then, env), _evaluate(node.else_, env))

    if isinstance(node, parser.Call):
        return Call(_evaluate(node.callee, env), [_evaluate(a, env) for a in node.args])

    if isinstance(node, parser.List):
        return List([_evaluate(e, env) for e in node.elems])

    raise EvalError(f'unknown: {type(node).__name__}', node)


# === Self-test ===

if __name__ == '__main__':
    src = r'''
$$double \(n : add(n, n)) !
$r1 double(3) !
$r2 double(add(1, 2)) !
$r3 double(3) !!

$id \(x : x) !
$r4 id(42) !

$$pair \(a b : [a, b]) !
$r5 pair(1, 2) !

$$compose \(f g : \(x : f(g(x)))) !
$r6 compose(double, double) !
$r7 compose(double, double)(3) !!

$$apply \(f x : f(x)) !
$r8 apply(double, 3) !

$abs \(n : ?(n, n, 0)) !
$r9 abs(True) !
$r10 abs(False) !

$$twice \(f : \(x : f(f(x)))) !
$r11 twice(double) !
$r12 twice(double)(3) !
$r13 \(f : \(x : f(x)))(double) !
$r14 \(x : double(x)) !!
$$addx \(x : \(y : add(x, y))) !
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
$f4 forall(\(x : mem(x, a))) !
$r30 same(f1, f1) !
$r31 same(f1, f2) !
'''
    env = global_()
    nodes = parser.parse(src, '<test>')
    for node in nodes:
        if isinstance(node, parser.Bind):
            val = evaluate(node.expr, env)
            show(val, node.name, node.show, node.traced)
            env.set(node.name, (val, node.traced))
