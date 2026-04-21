"""Database of formal definitions built on core."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


class DefSet:
    """P(S) = forall s. (forall x. x in s iff cond(x)) implies P(s)
    cond: lambda x -> formula describing membership"""

    def __init__(self, cond, body, prefix='set'):
        self.cond = cond
        self.var = Var(prefix)
        self.body = body

    def expand(self):
        x = Var()
        return Forall(self.var, Implies(
            Forall(x, Iff(In(x, self.var), self.cond(x))),
            self.body(self.var)))

    def __str__(self):
        return f'{self.body(self.var)}'


class Empty:
    """P(empty) = forall s. (forall x. not(x in s)) implies P(s)"""

    def __init__(self, body):
        self.var = Var('empty')
        self.body = body

    def expand(self):
        x = Var()
        return Forall(self.var, Implies(Forall(x, Not(In(x, self.var))), self.body(self.var)))

    def __str__(self):
        return f'{self.body(self.var)}'


def Singleton(a, body):
    """{a}: x in {a} iff x = a"""
    return DefSet(lambda x: Eq(x, a), body, 'sing')


def PairSet(a, b, body):
    """{a, b}: x in {a,b} iff x = a or x = b"""
    return DefSet(lambda x: Or(Eq(x, a), Eq(x, b)), body, 'pair')


def Tuple(a, b, body):
    """(a, b) = {{a}, {a, b}}"""
    return Singleton(a, lambda sa:
        PairSet(a, b, lambda pab:
            PairSet(sa, pab, body)))


