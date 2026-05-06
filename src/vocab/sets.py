"""Set vocabulary: basic set predicates and set operations."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


class SetSpec:
    """SetSpec(s, cond) = forall x. Iff(In(x, s), cond(x)). s has membership cond."""
    def __init__(self, s, cond):
        self.set = s
        self.cond = cond
    def expand(self):
        x = Var()
        return Forall(x, Iff(In(x, self.set), self.cond(x)))
    def subst(self, old, new):
        return SetSpec(new if self.set is old else self.set,
                       lambda x: self.cond(x).subst(old, new))
    def __str__(self):
        x = Var()
        return f'{self.set} = {{ {x} | {self.cond(x)} }}'


class Empty:
    """Empty(s) = forall x. not(x in s)"""
    __match_args__ = ('set',)
    def __init__(self, s):
        self.set = s
    def expand(self):
        x = Var()
        return Forall(x, Not(In(x, self.set)))
    def subst(self, old, new):
        return Empty(new if self.set is old else self.set)
    def __str__(self):
        return f'{self.set} = {{}}'


class Singleton:
    """Singleton(s, a) = forall x. Iff(In(x, s), Eq(x, a)). s is {a}."""
    __match_args__ = ('set', 'elem')
    def __init__(self, s, a, postfix=None):
        self.set = s; self.elem = a; self._postfix = postfix
    def expand(self):
        p = self._postfix
        x = Var(postfix=f'{p}.x' if p else None)
        return Forall(x, Iff(In(x, self.set), Eq(x, self.elem),
                             postfix=f'{p}.iff' if p else None),
                      postfix=f'{p}.fa' if p else None)
    def subst(self, old, new):
        return Singleton(new if self.set is old else self.set,
                         new if self.elem is old else self.elem)
    def __str__(self):
        s = f'{self.set} = {{{self.elem}}}'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class PairSet:
    """PairSet(s, a, b) = forall x. Iff(In(x, s), Or(Eq(x, a), Eq(x, b))). s is {a,b}."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b, postfix=None):
        self.set = s; self.left = a; self.right = b; self._postfix = postfix
    def expand(self):
        p = self._postfix
        x = Var(postfix=f'{p}.x' if p else None)
        return Forall(x, Iff(In(x, self.set), Or(Eq(x, self.left), Eq(x, self.right),
                                                  postfix=f'{p}.or' if p else None),
                             postfix=f'{p}.iff' if p else None),
                      postfix=f'{p}.fa' if p else None)
    def subst(self, old, new):
        return PairSet(new if self.set is old else self.set,
                       new if self.left is old else self.left,
                       new if self.right is old else self.right)
    def __str__(self):
        s = f'{self.set} = {{{self.left},{self.right}}}'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Subset:
    """Subset(a, b) = forall x. In(x, a) implies In(x, b). a sub b."""
    __match_args__ = ('left', 'right')
    def __init__(self, a, b):
        self.left = a
        self.right = b
    def expand(self):
        x = Var()
        return Forall(x, Implies(In(x, self.left), In(x, self.right)))
    def subst(self, old, new):
        return Subset(new if self.left is old else self.left,
                      new if self.right is old else self.right)
    def __str__(self):
        return f'{self.left} sub {self.right}'


class Union:
    """s = a | b"""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        return SetSpec(self.set, lambda z: Or(In(z, self.left), In(z, self.right)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Union(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} | {self.right}'

class Intersect:
    """s = a & b"""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        return SetSpec(self.set, lambda z: And(In(z, self.left), In(z, self.right)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Intersect(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} & {self.right}'

class BigUnion:
    """s = U(a)"""
    __match_args__ = ('set', 'family')
    def __init__(self, s, a):
        self.set = s; self.family = a
    def expand(self):
        y = Var()
        return SetSpec(self.set, lambda z: Exists(y, And(In(y, self.family), In(z, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return BigUnion(r(self.set), r(self.family))
    def __str__(self):
        return f'{self.set} = U({self.family})'

class BigIntersect:
    """s = I(a)"""
    __match_args__ = ('set', 'family')
    def __init__(self, s, a):
        self.set = s; self.family = a
    def expand(self):
        y = Var()
        return SetSpec(self.set, lambda z: Forall(y, Implies(In(y, self.family), In(z, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return BigIntersect(r(self.set), r(self.family))
    def __str__(self):
        return f'{self.set} = I({self.family})'

class PowerSet:
    """s = P(a)"""
    __match_args__ = ('set', 'of')
    def __init__(self, s, a):
        self.set = s; self.of = a
    def expand(self):
        return SetSpec(self.set, lambda z: Subset(z, self.of))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return PowerSet(r(self.set), r(self.of))
    def __str__(self):
        return f'{self.set} = P({self.of})'

class Diff:
    """s = a \\ b"""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        return SetSpec(self.set, lambda z: And(In(z, self.left), Not(In(z, self.right))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Diff(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} \\ {self.right}'

class Product:
    """Product(s, a, b): s = a x b (cartesian product).
    forall z. z in s iff exists x, y. x in a and y in b and OrdPair(z, x, y)."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        z, x, y = Var(), Var(), Var()
        from vocab.ordpair import OrdPair
        return Forall(z, Iff(In(z, self.set),
            Exists(x, Exists(y, And(In(x, self.left),
                And(In(y, self.right), OrdPair(z, x, y)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Product(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} x {self.right}'
