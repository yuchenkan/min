"""Derived connectives: classes with expansion to primitives."""

from core.lang import Var, In, Not, Implies, Forall


class Exists:
    __match_args__ = ('var', 'body')
    def __init__(self, var: Var, body):
        self.var = var
        self.body = body

    def expand(self):
        return Not(Forall(self.var, Not(self.body)))


class And:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def expand(self):
        return Not(Implies(self.left, Not(self.right)))


class Or:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def expand(self):
        return Implies(Not(self.left), self.right)


class Iff:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def expand(self):
        return Not(Implies(Implies(self.left, self.right), Not(Implies(self.right, self.left))))


class Eq:
    __match_args__ = ('left', 'right')
    def __init__(self, left: Var, right: Var):
        self.left = left
        self.right = right

    def expand(self):
        z = Var()
        a = Implies(In(z, self.left), In(z, self.right))
        b = Implies(In(z, self.right), In(z, self.left))
        return Forall(z, Not(Implies(a, Not(b))))


