"""First-order language of set theory."""


class Var:
    _counter = 0

    def __init__(self):
        Var._counter += 1
        self._id = Var._counter

    def __str__(self):
        return f'v.{self._id:x}'


class In:
    __match_args__ = ('left', 'right')
    def __init__(self, left: Var, right: Var):
        self.left = left
        self.right = right

    def subst(self, old: Var, new: Var):
        return In(new if self.left is old else self.left,
                  new if self.right is old else self.right)

    def __str__(self):
        return f'{self.left} in {self.right}'


class Not:
    __match_args__ = ('operand',)
    def __init__(self, operand: 'Formula'):
        self.operand = operand

    def subst(self, old: Var, new: Var):
        return Not(self.operand.subst(old, new))

    def __str__(self):
        return f'not ({self.operand})'


class Implies:
    __match_args__ = ('left', 'right')
    def __init__(self, left: 'Formula', right: 'Formula'):
        self.left = left
        self.right = right

    def subst(self, old: Var, new: Var):
        return Implies(self.left.subst(old, new), self.right.subst(old, new))

    def __str__(self):
        return f'({self.left}) implies ({self.right})'


class Forall:
    __match_args__ = ('var', 'body')
    def __init__(self, var: Var, body: 'Formula'):
        self.var = var
        self.body = body

    def subst(self, old: Var, new: Var):
        if self.var is old:
            return self
        return Forall(self.var, self.body.subst(old, new))

    def __str__(self):
        return f'forall {self.var}. ({self.body})'


Formula = In | Not | Implies | Forall
