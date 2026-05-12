"""Recursion vocabulary: TotalFrom, Recursive, RecApprox, Plus."""

from core.lang import Var, In, Implies, Forall
from core.derived import Exists, And, Iff, Eq
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
    Function(h) /\\ dom(h) = w /\\ h(0) = a /\\
    forall n in w. h(S(n)) = f(h(n)). w is omega."""
    __match_args__ = ('func', 'init', 'step', 'omega')
    def __init__(self, h, a, f, w):
        self.func = h; self.init = a; self.step = f; self.omega = w
    def expand(self):
        from vocab.functions import Domain
        e, n, val, sn, fval = Var(), Var(), Var(), Var(), Var()
        d = Var(postfix='_d')
        dom_eq = Forall(d, Implies(Domain(self.func, d), Eq(d, self.omega)))
        return And(Function(self.func),
               And(dom_eq,
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
        return f'Recursive({self.func}, {self.init}, {self.step}, {self.omega})'


class PlusFunc:
    """PlusFunc(h, w): h is the addition function over omega w.
    h : ω×ω → ω with h(⟨m,0⟩) = m and h(⟨m,S(n)⟩) = S(h(⟨m,n⟩)).

    And(Function(h),
    And(∀d,p. Domain(h,d) → Product(p,w,w) → Eq(d,p),
    And(∀m∈w. ∀z. Empty(z) → ∀pair. OrdPair(pair,m,z) → Apply(h,pair,m),
        ∀m∈w. ∀n∈w. ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h,pair,p) →
            ∀sn. Succ(sn,n) → ∀sp. Succ(sp,p) →
                ∀pair2. OrdPair(pair2,m,sn) → Apply(h,pair2,sp))))"""
    __match_args__ = ('func', 'omega')
    def __init__(self, h, w):
        self.func = h; self.omega = w
    def expand(self):
        from vocab.ordpair import OrdPair
        from vocab.functions import Domain
        from vocab.sets import Product
        m, n, z, p = Var(postfix='_m'), Var(postfix='_n'), Var(postfix='_z'), Var(postfix='_p')
        pair, pair2 = Var(postfix='_pair'), Var(postfix='_pair2')
        sn, sp = Var(postfix='_sn'), Var(postfix='_sp')
        d, prod = Var(postfix='_d'), Var(postfix='_prod')
        dom_eq = Forall(d, Forall(prod, Implies(Domain(self.func, d),
            Implies(Product(prod, self.omega, self.omega), Eq(d, prod)))))
        base = Forall(m, Implies(In(m, self.omega),
            Forall(z, Implies(Empty(z),
                Forall(pair, Implies(OrdPair(pair, m, z),
                    Apply(self.func, pair, m)))))))
        step = Forall(m, Implies(In(m, self.omega),
            Forall(n, Implies(In(n, self.omega),
                Forall(pair, Implies(OrdPair(pair, m, n),
                    Forall(p, Implies(Apply(self.func, pair, p),
                        Forall(sn, Implies(Successor(sn, n),
                            Forall(sp, Implies(Successor(sp, p),
                                Forall(pair2, Implies(OrdPair(pair2, m, sn),
                                    Apply(self.func, pair2, sp)))))))))))))))
        return And(Function(self.func), And(dom_eq, And(base, step)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return PlusFunc(r(self.func), r(self.omega))
    def __str__(self):
        return f'PlusFunc({self.func}, {self.omega})'


class Plus:
    """Plus(m, n, p): m + n = p.
    ∀w, h. Omega(w) → PlusFunc(h, w) → ∀pair. OrdPair(pair, m, n) → Apply(h, pair, p).
    For any addition function h, h(⟨m,n⟩) = p."""
    __match_args__ = ('left', 'right', 'result')
    def __init__(self, m, n, p):
        self.left = m; self.right = n; self.result = p
    def expand(self):
        from vocab.ordpair import OrdPair
        w, h, pair = Var(postfix='_w'), Var(postfix='_h'), Var(postfix='_pair')
        return Forall(w, Implies(Omega(w),
            Forall(h, Implies(PlusFunc(h, w),
                Forall(pair, Implies(OrdPair(pair, self.left, self.right),
                    Apply(h, pair, self.result)))))))
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
