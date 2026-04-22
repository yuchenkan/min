"""Database of formal definitions built on core."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


class SetSpec:
    """P(S) = forall s. (forall x. x in s iff cond(x)) implies P(s)
    cond: lambda x -> formula describing membership"""

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


class EmptySet:
    """P(empty) = forall s. (forall x. not(x in s)) implies P(s)"""

    def __init__(self, body):
        self.var = Var('{}')
        self.body = body

    def expand(self):
        x = Var()
        return Forall(self.var, Implies(Forall(x, Not(In(x, self.var))), self.body(self.var)))

    def __str__(self):
        return f'{self.body(self.var)}'


def Singleton(a, body, prefix=None):
    """{a}: x in {a} iff x = a"""
    return SetSpec(lambda x: Eq(x, a), body, prefix or f'{{{a}}}')


def PairSet(a, b, body, prefix=None):
    """{a, b}: x in {a,b} iff x = a or x = b"""
    return SetSpec(lambda x: Or(Eq(x, a), Eq(x, b)), body, prefix or f'{{{a},{b}}}')


def OrdPair(a, b, body):
    """(a, b) = {{a}, {a, b}}"""
    return Singleton(a, lambda sa:
        PairSet(a, b, lambda pab:
            PairSet(sa, pab, body, f'({a},{b})')))


# --- Section 4.1.4: Basic operations ---

class Subset:
    """a sub b = forall x. x in a implies x in b"""
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


# --- Section 4.2.1: Natural numbers ---

def Successor(x, body):
    """S(x) = x union {x}: z in S(x) iff z in x or z = x"""
    return SetSpec(lambda z: Or(In(z, x), Eq(z, x)), body, f'S({x})')


class IsInductive:
    """isInductive(a) = empty in a and forall x in a, S(x) in a"""
    __match_args__ = ('set',)
    def __init__(self, a):
        self.set = a
    def expand(self):
        x = Var()
        return And(
            EmptySet(lambda e: In(e, self.set)),
            Forall(x, Implies(In(x, self.set),
                Successor(x, lambda s: In(s, self.set)))))
    def subst(self, old, new):
        return IsInductive(new if self.set is old else self.set)
    def __str__(self):
        return f'Inductive({self.set})'


class Omega:
    """P(omega). omega = smallest inductive set.
    forall b. isInductive(b) implies
      forall a. (a = {x in b : x in every inductive set}) implies P(a)"""
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

