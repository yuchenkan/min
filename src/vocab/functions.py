"""Function vocabulary: Apply, Domain, Range, Relation, Function, Total."""

from core.lang import Var, In, Implies, Forall
from core.derived import Exists, And, Iff, Eq
from vocab.ordpair import OrdPair


class Apply:
    """Apply(f, x, y): f(x) = y, i.e. <x,y> in f."""
    __match_args__ = ('func', 'arg', 'val')
    def __init__(self, f, x, y):
        self.func = f; self.arg = x; self.val = y
    def expand(self):
        p = Var()
        return Exists(p, And(OrdPair(p, self.arg, self.val), In(p, self.func)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Apply(r(self.func), r(self.arg), r(self.val))
    def __str__(self):
        return f'{self.func}({self.arg}) = {self.val}'


class Domain:
    """Domain(f, d): d = dom(f). forall x. x in d iff exists y. Apply(f, x, y)."""
    __match_args__ = ('func', 'set')
    def __init__(self, f, d):
        self.func = f; self.set = d
    def expand(self):
        x, y = Var(), Var()
        return Forall(x, Iff(In(x, self.set), Exists(y, Apply(self.func, x, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Domain(r(self.func), r(self.set))
    def __str__(self):
        return f'{self.set} = dom({self.func})'


class Range:
    """Range(f, r): r = ran(f). forall y. y in r iff exists x. Apply(f, x, y)."""
    __match_args__ = ('func', 'set')
    def __init__(self, f, r):
        self.func = f; self.set = r
    def expand(self):
        x, y = Var(), Var()
        return Forall(y, Iff(In(y, self.set), Exists(x, Apply(self.func, x, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Range(r(self.func), r(self.set))
    def __str__(self):
        return f'{self.set} = ran({self.func})'


class Relation:
    """Relation(r): all elements of r are ordered pairs.
    forall z. z in r -> exists x, y. OrdPair(z, x, y)."""
    __match_args__ = ('set',)
    def __init__(self, r):
        self.set = r
    def expand(self):
        z, x, y = Var(), Var(), Var()
        return Forall(z, Implies(In(z, self.set),
            Exists(x, Exists(y, OrdPair(z, x, y)))))
    def subst(self, old, new):
        return Relation(new if self.set is old else self.set)
    def __str__(self):
        return f'Relation({self.set})'


class Function:
    """Function(f): f is a relation and single-valued.
    Relation(f) and forall x, y1, y2. Apply(f,x,y1) and Apply(f,x,y2) -> y1 = y2."""
    __match_args__ = ('set',)
    def __init__(self, f):
        self.set = f
    def expand(self):
        x, y1, y2 = Var(), Var(), Var()
        single_valued = Forall(x, Forall(y1, Forall(y2,
            Implies(And(Apply(self.set, x, y1), Apply(self.set, x, y2)),
                    Eq(y1, y2)))))
        return And(Relation(self.set), single_valued)
    def subst(self, old, new):
        return Function(new if self.set is old else self.set)
    def __str__(self):
        return f'Function({self.set})'


class Total:
    """Total(f, a): f is total on a. forall x. x in a -> exists y. Apply(f, x, y)."""
    __match_args__ = ('func', 'domain')
    def __init__(self, f, a):
        self.func = f; self.domain = a
    def expand(self):
        x, y = Var(), Var()
        return Forall(x, Implies(In(x, self.domain), Exists(y, Apply(self.func, x, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Total(r(self.func), r(self.domain))
    def __str__(self):
        return f'Total({self.func}, {self.domain})'
