"""First-order language of set theory."""


class Var:
    pass


class In:
    __match_args__ = ('left', 'right')
    def __init__(self, left: Var, right: Var):
        self.left = left
        self.right = right


class Not:
    __match_args__ = ('operand',)
    def __init__(self, operand: 'Formula'):
        self.operand = operand


class Implies:
    __match_args__ = ('left', 'right')
    def __init__(self, left: 'Formula', right: 'Formula'):
        self.left = left
        self.right = right


class Forall:
    __match_args__ = ('var', 'body')
    def __init__(self, var: Var, body: 'Formula'):
        self.var = var
        self.body = body


Formula = In | Not | Implies | Forall
