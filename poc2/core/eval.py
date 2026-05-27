"""Node-based eval. Everything is a Node(tag, children) or a leaf (int, bool)."""

import os, sys, parser

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
        return self.body.rewrite(dict(zip(self.params, args)))

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
        return f'_add({_show(v.a, depth)}, {_show(v.b, depth)})'


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
        if isinstance(self.a, Val) and isinstance(self.b, Val):
            return Val(self.a.val + self.b.val)
        return self

def add():
    a = Param('a')
    b = Param('b')
    return Fn(Add(a, b), [a, b])


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
    e.set('True', (Val(True), False))
    e.set('False', (Val(False), False))
    e.set('add', (add(), True))
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
'''
    env = global_()
    nodes = parser.parse(src, '<test>')
    for node in nodes:
        if isinstance(node, parser.Bind):
            val = evaluate(node.expr, env)
            show(val, node.name, node.show, node.traced)
            env.set(node.name, (val, node.traced))
