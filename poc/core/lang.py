"""Core language: Var, In, Not, Implies, Forall.

Var(bound=True) marks a binding variable.
All Var compared by identity (is).
"""


class Var:
    def __init__(self, name=None, bound=False):
        self.name = name
        self.bound = bound


class In:
    def __init__(self, left, right):
        assert isinstance(left, Var), f'In.left must be Var, got {type(left).__name__}'
        assert isinstance(right, Var), f'In.right must be Var, got {type(right).__name__}'
        self.left = left
        self.right = right


class Not:
    def __init__(self, operand):
        assert isinstance(operand, (In, Not, Implies, Forall)), f'Not.operand must be formula, got {type(operand).__name__}'
        self.operand = operand


class Implies:
    def __init__(self, left, right):
        assert isinstance(left, (In, Not, Implies, Forall)), f'Implies.left must be formula, got {type(left).__name__}'
        assert isinstance(right, (In, Not, Implies, Forall)), f'Implies.right must be formula, got {type(right).__name__}'
        self.left = left
        self.right = right


class Forall:
    def __init__(self, var, body):
        assert isinstance(var, Var) and var.bound, f'Forall.var must be Var(bound=True), got {var}'
        assert isinstance(body, (In, Not, Implies, Forall)), f'Forall.body must be formula, got {type(body).__name__}'
        self.var = var
        self.body = body
