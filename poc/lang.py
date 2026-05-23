"""Core language: Var, In, Not, Implies, Forall.

Immutable. No caching, no mutation.
All Var compared by identity (is).
Var(bound=True) marks a binding variable — display/type hint only.
"""


class Var:
    __slots__ = ('name', 'bound')
    def __init__(self, name=None, bound=False):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'bound', bound)
    def __setattr__(self, *_):
        raise AttributeError('immutable')
    def __delattr__(self, *_):
        raise AttributeError('immutable')


class In:
    __slots__ = ('left', 'right')
    def __init__(self, left, right):
        object.__setattr__(self, 'left', left)
        object.__setattr__(self, 'right', right)
    def __setattr__(self, *_):
        raise AttributeError('immutable')
    def __delattr__(self, *_):
        raise AttributeError('immutable')


class Not:
    __slots__ = ('operand',)
    def __init__(self, operand):
        object.__setattr__(self, 'operand', operand)
    def __setattr__(self, *_):
        raise AttributeError('immutable')
    def __delattr__(self, *_):
        raise AttributeError('immutable')


class Implies:
    __slots__ = ('left', 'right')
    def __init__(self, left, right):
        object.__setattr__(self, 'left', left)
        object.__setattr__(self, 'right', right)
    def __setattr__(self, *_):
        raise AttributeError('immutable')
    def __delattr__(self, *_):
        raise AttributeError('immutable')


class Forall:
    __slots__ = ('var', 'body')
    def __init__(self, var, body):
        object.__setattr__(self, 'var', var)
        object.__setattr__(self, 'body', body)
    def __setattr__(self, *_):
        raise AttributeError('immutable')
    def __delattr__(self, *_):
        raise AttributeError('immutable')
