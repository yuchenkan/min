"""Core language: Var, In, Not, Implies, Forall.

All Var compared by identity (is).
"""


class Var:
    pass


class In:
    def __init__(self, left, right):
        self.left = left
        self.right = right


class Not:
    def __init__(self, operand):
        self.operand = operand


class Implies:
    def __init__(self, left, right):
        self.left = left
        self.right = right


class Forall:
    def __init__(self, var, body):
        self.var = var
        self.body = body
