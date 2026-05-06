"""Ordered pair and successor."""

from core.lang import Var, In, Implies, Forall
from core.derived import Or, Iff, Eq
from vocab.sets import Singleton, PairSet


class OrdPair:
    """OrdPair(t, a, b): t = (a, b) = {{a}, {a, b}}.
    Forall sa. Singleton(sa,a) -> Forall pab. PairSet(pab,a,b) -> PairSet(t,sa,pab)."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, t, a, b, postfix=None):
        self.set = t; self.left = a; self.right = b; self._postfix = postfix
    def expand(self):
        p = self._postfix
        sa = Var(postfix=f'{p}.sa' if p else None)
        pab = Var(postfix=f'{p}.pab' if p else None)
        return Forall(sa, Implies(Singleton(sa, self.left, postfix=f'{p}.sing' if p else None),
            Forall(pab, Implies(PairSet(pab, self.left, self.right, postfix=f'{p}.ps_ab' if p else None),
                PairSet(self.set, sa, pab, postfix=f'{p}.ps_t' if p else None)))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return OrdPair(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        s = f'{self.set} = <{self.left},{self.right}>'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Successor:
    """Successor(s, x) = forall z. Iff(In(z, s), Or(In(z, x), Eq(z, x))). s is S(x) = x union {x}."""
    __match_args__ = ('set', 'of')
    def __init__(self, s, x):
        self.set = s
        self.of = x
    def expand(self):
        z = Var()
        return Forall(z, Iff(In(z, self.set), Or(In(z, self.of), Eq(z, self.of))))
    def subst(self, old, new):
        return Successor(new if self.set is old else self.set,
                         new if self.of is old else self.of)
    def __str__(self):
        return f'{self.set} = S({self.of})'
