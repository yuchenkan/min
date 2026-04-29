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
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f'{self.left} in {self.right}'


class Not:
    __match_args__ = ('operand',)
    def __init__(self, operand):
        self.operand = operand

    def __str__(self):
        return f'not ({self.operand})'


class Implies:
    __match_args__ = ('left', 'right')
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f'({self.left}) implies ({self.right})'


class Forall:
    __match_args__ = ('var', 'body')
    def __init__(self, var, body):
        self.var = var
        self.body = body

    def __str__(self):
        return f'forall {self.var}. ({self.body})'


Formula = In | Not | Implies | Forall
