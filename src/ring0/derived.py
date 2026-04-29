"""Derived connectives: classes with expansion to primitives."""

from ring0.lang import Var, In, Not, Implies, Forall


class Exists:
    __match_args__ = ('var', 'body')
    def __init__(self, var: Var, body, postfix=None):
        self.var = var
        self.body = body
        self._postfix = postfix

    def expand(self):
        p = self._postfix
        return Not(Forall(self.var, Not(self.body, postfix=f'{p}.body' if p else None),
                          postfix=f'{p}.fa' if p else None),
                   postfix=f'{p}.not' if p else None)

    def subst(self, old: Var, new: Var):
        if self.var is old:
            return self
        return Exists(self.var, self.body.subst(old, new))

    def __str__(self):
        s = f'exists {self.var}. ({self.body})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class And:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right, postfix=None):
        self.left = left
        self.right = right
        self._postfix = postfix

    def expand(self):
        p = self._postfix
        return Not(Implies(self.left, Not(self.right, postfix=f'{p}.nr' if p else None),
                           postfix=f'{p}.imp' if p else None),
                   postfix=f'{p}.not' if p else None)

    def subst(self, old: Var, new: Var):
        return And(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        s = f'({self.left}) and ({self.right})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Or:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right, postfix=None):
        self.left = left
        self.right = right
        self._postfix = postfix

    def expand(self):
        p = self._postfix
        return Implies(Not(self.left, postfix=f'{p}.nl' if p else None), self.right,
                       postfix=f'{p}.imp' if p else None)

    def subst(self, old: Var, new: Var):
        return Or(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        s = f'({self.left}) or ({self.right})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Iff:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right, postfix=None):
        self.left = left
        self.right = right
        self._postfix = postfix

    def expand(self):
        p = self._postfix
        fwd = Implies(self.left, self.right, postfix=f'{p}.fwd' if p else None)
        bwd = Implies(self.right, self.left, postfix=f'{p}.bwd' if p else None)
        return Not(Implies(fwd, Not(bwd, postfix=f'{p}.nbwd' if p else None),
                           postfix=f'{p}.imp' if p else None),
                   postfix=f'{p}.not' if p else None)

    def subst(self, old: Var, new: Var):
        return Iff(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        s = f'({self.left}) iff ({self.right})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Eq:
    __match_args__ = ('left', 'right')
    def __init__(self, left: Var, right: Var, postfix=None):
        self.left = left
        self.right = right
        self._postfix = postfix

    def expand(self):
        p = self._postfix
        z = Var(postfix=f'{p}.z' if p else None)
        a = Implies(In(z, self.left), In(z, self.right), postfix=f'{p}.fwd' if p else None)
        b = Implies(In(z, self.right), In(z, self.left), postfix=f'{p}.bwd' if p else None)
        return Forall(z, Not(Implies(a, Not(b, postfix=f'{p}.nb' if p else None),
                                     postfix=f'{p}.imp' if p else None),
                             postfix=f'{p}.body' if p else None),
                      postfix=f'{p}.fa' if p else None)

    def subst(self, old: Var, new: Var):
        return Eq(new if self.left is old else self.left,
                  new if self.right is old else self.right)

    def __str__(self):
        s = f'{self.left} = {self.right}'
        return f'{s}/*{self._postfix}*/' if self._postfix else s
