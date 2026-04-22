"""Database of formal definitions built on core.

Naming convention:
- Predicates (Empty, Singleton, PairSet, Successor, Inductive, Subset):
  formula-level objects describing a property of sets.
- Compound definitions (OrdPair, Omega):
  build formulas using predicates + Forall/Implies.
- SetSpec: generic definite description for unnamed set constructions
  (Union, Intersect, PowerSet, Diff, BigUnion, BigIntersect).
"""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


# --- Generic set characterization predicate ---

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


# --- Predicates ---

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
    def __init__(self, s, a):
        self.set = s
        self.elem = a
    def expand(self):
        x = Var()
        return Forall(x, Iff(In(x, self.set), Eq(x, self.elem)))
    def subst(self, old, new):
        return Singleton(new if self.set is old else self.set,
                         new if self.elem is old else self.elem)
    def __str__(self):
        return f'{self.set} = {{{self.elem}}}'


class PairSet:
    """PairSet(s, a, b) = forall x. Iff(In(x, s), Or(Eq(x, a), Eq(x, b))). s is {a,b}."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s
        self.left = a
        self.right = b
    def expand(self):
        x = Var()
        return Forall(x, Iff(In(x, self.set), Or(Eq(x, self.left), Eq(x, self.right))))
    def subst(self, old, new):
        return PairSet(new if self.set is old else self.set,
                       new if self.left is old else self.left,
                       new if self.right is old else self.right)
    def __str__(self):
        return f'{self.set} = {{{self.left},{self.right}}}'


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


# --- Compound definitions ---

class OrdPair:
    """OrdPair(t, a, b): t = (a, b) = {{a}, {a, b}}.
    Exists sa. Singleton(sa,a) and Exists pab. PairSet(pab,a,b) and PairSet(t,sa,pab)."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, t, a, b):
        self.set = t; self.left = a; self.right = b
    def expand(self):
        sa = Var()
        pab = Var()
        return Exists(sa, And(Singleton(sa, self.left),
            Exists(pab, And(PairSet(pab, self.left, self.right),
                PairSet(self.set, sa, pab)))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return OrdPair(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = <{self.left},{self.right}>'


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


# --- Set operation predicates ---

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


