"""Recursion vocabulary: TotalFrom, Recursive, RecApprox, Plus."""

from core.lang import Var, In, Implies, Forall
from core.derived import Exists, And, Iff
from vocab.sets import Empty
from vocab.ordpair import Successor
from vocab.functions import Apply, Function
from vocab.omega import Omega


class TotalFrom:
    """TotalFrom(f, a): f is defined at a and range-closed.
    And(Exists(z, Apply(f,a,z)), Forall(x, Forall(y, Implies(Apply(f,x,y), Exists(z, Apply(f,y,z))))))"""
    __match_args__ = ('func', 'init')
    def __init__(self, f, a):
        self.func = f; self.init = a
    def expand(self):
        z, x, y = Var(), Var(), Var()
        return And(Exists(z, Apply(self.func, self.init, z)),
                   Forall(x, Forall(y, Implies(Apply(self.func, x, y),
                       Exists(z, Apply(self.func, y, z))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TotalFrom(r(self.func), r(self.init))
    def __str__(self):
        return f'TotalFrom({self.func}, {self.init})'


class Recursive:
    """Recursive(h, a, f, w): isRecursive per book Thm 4.2.14.
    Function(h) /\\ dom(h) <= w /\\ h(0) = a /\\
    forall n in w. h(S(n)) = f(h(n)). w is omega."""
    __match_args__ = ('func', 'init', 'step', 'omega')
    def __init__(self, h, a, f, w):
        self.func = h; self.init = a; self.step = f; self.omega = w
    def expand(self):
        e, n, val, sn, fval, xd, yd = Var(), Var(), Var(), Var(), Var(), Var(), Var()
        dom_sub = Forall(xd, Implies(Exists(yd, Apply(self.func, xd, yd)),
                                     In(xd, self.omega)))
        return And(Function(self.func),
               And(dom_sub,
               And(Forall(e, Implies(Empty(e), Apply(self.func, e, self.init))),
                   Forall(n, Implies(In(n, self.omega),
                       Forall(val, Implies(Apply(self.func, n, val),
                           Forall(sn, Implies(Successor(sn, n),
                               Forall(fval, Implies(Apply(self.step, val, fval),
                                   Apply(self.func, sn, fval))))))))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Recursive(r(self.func), r(self.init), r(self.step), r(self.omega))
    def __str__(self):
        return f'Recursive({self.func}, {self.init}, {self.step})'


class Plus:
    """Plus(m, n, p): m + n = p.
    Exists w, h, sf. Omega(w) and sf_props(sf,w) and Recursive(h, m, sf, w) and Apply(h, n, p).
    sf_props(sf,w) = succ_char(sf,w) /\\ Function(sf) /\\ dom_sub(sf,w)."""
    __match_args__ = ('left', 'right', 'result')
    def __init__(self, m, n, p):
        self.left = m; self.right = n; self.result = p
    def expand(self):
        w, h, sf, x, y, xd, yd = Var(), Var(), Var(), Var(), Var(), Var(), Var()
        succ_char = Forall(x, Implies(In(x, w),
            Forall(y, Iff(Apply(sf, x, y), Successor(y, x)))))
        sf_all = And(succ_char, And(Function(sf),
            Forall(xd, Implies(Exists(yd, Apply(sf, xd, yd)), In(xd, w)))))
        return Exists(w, And(Omega(w),
            Exists(h, Exists(sf,
                And(sf_all,
                And(Recursive(h, self.left, sf, w),
                    Apply(h, self.right, self.result)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Plus(r(self.left), r(self.right), r(self.result))
    def __str__(self):
        return f'{self.left} + {self.right} = {self.result}'


class RecApprox:
    """RecApprox(v, a, f, w): v is a recursive approximation (book P(v), Thm 4.2.14).
    Function(v) and Subset(dom v, w) and ran v sub dom f
    and base and step conditions."""
    __match_args__ = ('func', 'init', 'step', 'omega')
    def __init__(self, v, a, f, w):
        self.func = v; self.init = a; self.step = f; self.omega = w
    def expand(self):
        e, n, sn, val, fval, y, x, z = Var(), Var(), Var(), Var(), Var(), Var(), Var(), Var()
        func_v = Function(self.func)
        dom_sub_w = Forall(x, Implies(Exists(y, Apply(self.func, x, y)),
                                       In(x, self.omega)))
        ran_sub_dom = Forall(x, Forall(y, Implies(Apply(self.func, x, y),
                                                    Exists(z, Apply(self.step, y, z)))))
        base = Forall(e, Implies(Empty(e),
                   Implies(Exists(y, Apply(self.func, e, y)),
                           Apply(self.func, e, self.init))))
        step = Forall(n, Implies(In(n, self.omega),
                   Forall(sn, Implies(Successor(sn, n),
                       Implies(Exists(y, Apply(self.func, sn, y)),
                           And(Exists(y, Apply(self.func, n, y)),
                               Forall(val, Implies(Apply(self.func, n, val),
                                   Forall(fval, Implies(Apply(self.step, val, fval),
                                       Apply(self.func, sn, fval)))))))))))
        return And(func_v, And(dom_sub_w, And(ran_sub_dom, And(base, step))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return RecApprox(r(self.func), r(self.init), r(self.step), r(self.omega))
    def __str__(self):
        return f'RecApprox({self.func}, {self.init}, {self.step}, {self.omega})'
