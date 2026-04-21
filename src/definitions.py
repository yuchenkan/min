"""Database of formal definitions built on core."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


class Empty:
    """P(empty) = forall b. (forall x. not (x in b)) implies P(b)"""

    def __init__(self, body):
        self.var = Var('empty')
        self.body = body

    def expand(self):
        x = Var()
        return Forall(self.var, Implies(Forall(x, Not(In(x, self.var))), self.body(self.var)))

    def __str__(self):
        return f'{self.body(self.var)}'
