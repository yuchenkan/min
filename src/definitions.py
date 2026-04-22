"""Database of formal definitions built on core.

Naming convention:
- Predicates (Empty, Singleton, PairSet, Successor, IsInductive, Subset):
  formula-level objects describing a property of sets.
- Compound definitions (OrdPair, Omega):
  build formulas using predicates + Forall/Implies.
- SetSpec: generic definite description for unnamed set constructions
  (Union, Intersect, PowerSet, Diff, BigUnion, BigIntersect).
"""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


# --- Generic definite description (for unnamed sets) ---

class SetSpec:
    """forall s. (forall x. x in s iff cond(x)) implies body(s)"""
    def __init__(self, cond, body, prefix=None):
        self.cond = cond
        self.body = body
        if prefix is None:
            x = Var()
            prefix = f'{{{x}|{cond(x)}}}'
        self.var = Var(prefix)
    def expand(self):
        x = Var()
        return Forall(self.var, Implies(
            Forall(x, Iff(In(x, self.var), self.cond(x))),
            self.body(self.var)))
    def __str__(self):
        return f'{self.body(self.var)}'


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


class IsInductive:
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
        return IsInductive(new if self.set is old else self.set)
    def __str__(self):
        return f'Inductive({self.set})'


# --- Compound definitions ---

def OrdPair(a, b, body):
    """(a, b) = {{a}, {a, b}}. Kuratowski ordered pair."""
    sa = Var(f'{{{a}}}')
    pab = Var(f'{{{a},{b}}}')
    t = Var(f'({a},{b})')
    return Forall(sa, Implies(Singleton(sa, a),
        Forall(pab, Implies(PairSet(pab, a, b),
            Forall(t, Implies(PairSet(t, sa, pab), body(t)))))))


class Omega:
    """P(omega). omega = smallest inductive set.
    forall b. isInductive(b) implies
      forall a. (forall x. x in a iff (x in b and forall c. isInductive(c) implies x in c))
        implies P(a)"""
    def __init__(self, body):
        self.body = body
    def expand(self):
        b, a, x, c = Var(), Var(), Var(), Var()
        cond = And(In(x, b), Forall(c, Implies(IsInductive(c), In(x, c))))
        char_a = Forall(x, Iff(In(x, a), cond))
        return Forall(b, Implies(IsInductive(b),
            Forall(a, Implies(char_a, self.body(a)))))
    def __str__(self):
        v = Var('omega')
        return f'{self.body(v)}'


# --- Set operations (use SetSpec for unnamed constructions) ---

def Union(a, b, body):
    """a union b: z in a|b iff z in a or z in b"""
    return SetSpec(lambda z: Or(In(z, a), In(z, b)), body, f'{a}|{b}')


def BigUnion(a, body):
    """Union of family: z in U(a) iff exists y in a with z in y"""
    y = Var()
    return SetSpec(lambda z: Exists(y, And(In(y, a), In(z, y))), body, f'U({a})')


def Intersect(a, b, body):
    """a intersect b: z in a&b iff z in a and z in b"""
    return SetSpec(lambda z: And(In(z, a), In(z, b)), body, f'{a}&{b}')


def BigIntersect(a, body):
    """Intersection of family: z in I(a) iff forall y in a, z in y"""
    y = Var()
    return SetSpec(lambda z: Forall(y, Implies(In(y, a), In(z, y))), body, f'I({a})')


def PowerSet(a, body):
    """Power set: z in P(a) iff z sub a"""
    return SetSpec(lambda z: Subset(z, a), body, f'P({a})')


def Diff(a, b, body):
    """Set difference: z in a\\b iff z in a and not z in b"""
    return SetSpec(lambda z: And(In(z, a), Not(In(z, b))), body, f'{a}\\{b}')


