"""Derived connectives: classes with expansion to primitives."""

from core.lang import Var, In, Not, Implies, Forall


class Exists:
    __match_args__ = ('var', 'body')
    def __init__(self, var: Var, body):
        self.var = var
        self.body = body

    def expand(self):
        return Not(Forall(self.var, Not(self.body)))

    def subst(self, old: Var, new: Var):
        if self.var is old:
            return self
        return Exists(self.var, self.body.subst(old, new))

    def __str__(self):
        return f'exists {self.var}. ({self.body})'


class And:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def expand(self):
        return Not(Implies(self.left, Not(self.right)))

    def subst(self, old: Var, new: Var):
        return And(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        return f'({self.left}) and ({self.right})'


class Or:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def expand(self):
        return Implies(Not(self.left), self.right)

    def subst(self, old: Var, new: Var):
        return Or(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        return f'({self.left}) or ({self.right})'


class Iff:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def expand(self):
        return Not(Implies(Implies(self.left, self.right), Not(Implies(self.right, self.left))))

    def subst(self, old: Var, new: Var):
        return Iff(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        return f'({self.left}) iff ({self.right})'


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

    def subst(self, old: Var, new: Var):
        return Eq(new if self.left is old else self.left,
                  new if self.right is old else self.right)

    def __str__(self):
        return f'{self.left} = {self.right}'
