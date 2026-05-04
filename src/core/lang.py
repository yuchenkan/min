"""First-order language of set theory."""


class Var:
    _counter = 0

    def __init__(self, postfix=None):
        Var._counter += 1
        self._id = Var._counter
        self._postfix = postfix

    def eq(self, other, env, expand, eq):
        for v1, v2 in env:
            if self is v1: return other is v2
            if other is v2: return False
        return self is other

    def __str__(self):
        s = f'v.{self._id:x}'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class In:
    __match_args__ = ('left', 'right')
    def __init__(self, left: Var, right: Var, postfix=None):
        self.left = left
        self.right = right
        self._postfix = postfix

    def subst(self, old: Var, new: Var):
        return In(new if self.left is old else self.left,
                  new if self.right is old else self.right)

    def __str__(self):
        s = f'{self.left} in {self.right}'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Not:
    __match_args__ = ('operand',)
    def __init__(self, operand: 'Formula', postfix=None):
        self.operand = operand
        self._postfix = postfix

    def subst(self, old: Var, new: Var):
        return Not(self.operand.subst(old, new))

    def __str__(self):
        s = f'not ({self.operand})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Implies:
    __match_args__ = ('left', 'right')
    def __init__(self, left: 'Formula', right: 'Formula', postfix=None):
        self.left = left
        self.right = right
        self._postfix = postfix

    def subst(self, old: Var, new: Var):
        return Implies(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        s = f'({self.left}) implies ({self.right})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


class Forall:
    __match_args__ = ('var', 'body')
    def __init__(self, var: Var, body: 'Formula', postfix=None):
        self.var = var
        self.body = body
        self._postfix = postfix

    def eq(self, other, env, expand, eq):
        return eq(self.body, other.body, env + [(self.var, other.var)], expand)

    def subst(self, old: Var, new: Var):
        if self.var is old:
            return self
        return Forall(self.var, self.body.subst(old, new))

    def __str__(self):
        s = f'forall {self.var}. ({self.body})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


Formula = In | Not | Implies | Forall
