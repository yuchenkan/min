"""Omega vocabulary: Inductive, Omega, Nat, Num, ExistsUnique."""

from core.lang import Var, In, Implies, Forall
from core.derived import Exists, And, Iff, Eq
from vocab.sets import Empty
from vocab.ordpair import Successor


class Inductive:
    """isInductive(a) = (forall e. Empty(e) implies e in a)
                      and (forall x in a. forall s. Successor(s, x) implies s in a)"""
    __match_args__ = ('set',)
    def __init__(self, a):
        self.set = a
    def expand(self):
        e, x, s = Var(), Var(), Var()
        return And(
            Forall(e, Implies(Empty(e), In(e, self.set))),
            Forall(x, Implies(In(x, self.set),
                Forall(s, Implies(Successor(s, x), In(s, self.set))))))
    def subst(self, old, new):
        return Inductive(new if self.set is old else self.set)
    def __str__(self):
        return f'Inductive({self.set})'


class Omega:
    """Omega(w): w is the smallest inductive set.
    forall b. isInductive(b) implies forall x. x in w iff (x in b and forall c. isInductive(c) implies x in c)"""
    __match_args__ = ('set',)
    def __init__(self, w):
        self.set = w
    def expand(self):
        b, x, c = Var(), Var(), Var()
        cond = And(In(x, b), Forall(c, Implies(Inductive(c), In(x, c))))
        return Forall(b, Implies(Inductive(b),
            Forall(x, Iff(In(x, self.set), cond))))
    def subst(self, old, new):
        return Omega(new if self.set is old else self.set)
    def __str__(self):
        return f'{self.set} = omega'


class Nat:
    """Nat(n): n is a natural number (n in omega).
    exists w. Omega(w) and In(n, w)."""
    __match_args__ = ('elem',)
    def __init__(self, n):
        self.elem = n
    def expand(self):
        w = Var()
        return Exists(w, And(Omega(w), In(self.elem, w)))
    def subst(self, old, new):
        return Nat(new if self.elem is old else self.elem)
    def __str__(self):
        return f'{self.elem} in N'


class Num:
    """Num(n, k): n equals the natural number k (k is a Python int).
    Num(n, 0) = Empty(n)
    Num(n, k+1) = exists m. Num(m, k) and Successor(n, m)"""
    __match_args__ = ('elem', 'value')
    def __init__(self, n, k):
        self.elem = n
        self.value = k
    def expand(self):
        if self.value == 0:
            return Empty(self.elem)
        m = Var()
        return Exists(m, And(Num(m, self.value - 1), Successor(self.elem, m)))
    def subst(self, old, new):
        return Num(new if self.elem is old else self.elem, self.value)
    def __str__(self):
        return f'{self.elem} = {self.value}'


class ExistsUnique:
    """ExistsUnique(var, body): exists unique var satisfying body.
    exists var. body and forall var'. body[var:=var'] -> Eq(var, var')"""
    __match_args__ = ('var', 'body')
    def __init__(self, var, body, postfix=None):
        self.var = var
        self.body = body
        self._postfix = postfix

    def expand(self):
        p = self._postfix
        v2 = Var(postfix=f'{p}.v2' if p else None)
        body_v2 = self.body.subst(self.var, v2)
        unique = Forall(v2, Implies(body_v2, Eq(self.var, v2),
                                    postfix=f'{p}.imp' if p else None),
                        postfix=f'{p}.fa' if p else None)
        return Exists(self.var, And(self.body, unique, postfix=f'{p}.and' if p else None),
                      postfix=f'{p}.ex' if p else None)

    def subst(self, old, new):
        if self.var is old:
            return self
        return ExistsUnique(self.var, self.body.subst(old, new))

    def __str__(self):
        s = f'exists! {self.var}. ({self.body})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s
