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

